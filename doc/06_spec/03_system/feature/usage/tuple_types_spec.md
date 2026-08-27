# Tuple Types Specification

> Tuple types are ordered collections of heterogeneous values with fixed length. They allow grouping multiple values of different types without defining a named struct, useful for returning multiple values or temporary groupings.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tuple Types Specification

Tuple types are ordered collections of heterogeneous values with fixed length. They allow grouping multiple values of different types without defining a named struct, useful for returning multiple values or temporary groupings.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TBD |
| Category | Language |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/tuple_types_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tuple types are ordered collections of heterogeneous values with fixed length.
They allow grouping multiple values of different types without defining a
named struct, useful for returning multiple values or temporary groupings.

## Syntax

```simple
use std.spec.step

val point = (3, 4)
val mixed = ("hello", 42, true)
val (x, y) = point  # Destructuring
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Tuple | Fixed-size heterogeneous collection |
| Tuple Type | Type annotation like `(T1, T2, T3)` |
| Destructuring | Pattern matching to extract tuple elements |
| Unit Type | Empty tuple `()` representing no value |

## Behavior

- Tuples have fixed length determined at compile time
- Elements accessed by index: `tuple[0]`, `tuple[1]`
- Support pattern matching and destructuring
- Unit type `()` is the zero-element tuple

## Scenarios

### Tuple Types

#### tuple creation

#### creates tuple literal

- creates tuple literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates tuple literal")
val t = (10, 20, 30)
expect t[1] == 20
```

</details>

#### gets tuple length

- gets tuple length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gets tuple length")
val t = (1, 2, 3, 4)
expect t.len() == 4
```

</details>

#### tuple access

#### accesses elements by index

- accesses elements by index


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accesses elements by index")
val t = (5, 10, 15)
expect t[0] == 5
expect t[2] == 15
```

</details>

#### tuple destructuring

#### destructures tuple into variables

- destructures tuple into variables


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("destructures tuple into variables")
val (a, b, c) = (10, 20, 30)
expect a + b + c == 60
```

</details>

#### swaps values with tuple destructuring

- swaps values with tuple destructuring


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("swaps values with tuple destructuring")
val a = 10
val b = 20
val (x, y) = (b, a)
expect x == 20
```

</details>

#### destructures from array

- destructures from array


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("destructures from array")
val arr = [5, 10, 15]
val (first, second, third) = arr
expect second == 10
```

</details>

### Tuple Pattern Matching

#### matches tuple pattern

- matches tuple pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches tuple pattern")
val t = (1, 2)
val result = match t:
    (1, x) => x * 10
    _ => 0
expect result == 20
```

</details>

#### uses wildcard for unmatched tuples

- uses wildcard for unmatched tuples


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses wildcard for unmatched tuples")
val t = (5, 5)
val result = match t:
    (1, x) => x
    _ => 99
expect result == 99
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `aa32a294f8aa1c9771c535c40e734877077f662cf359a7b8fb934f84978a82ab`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aa32a294f8aa1c9771c535c40e734877077f662cf359a7b8fb934f84978a82ab`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aa32a294f8aa1c9771c535c40e734877077f662cf359a7b8fb934f84978a82ab`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/tuple_types_spec.spl
mirror: doc/06_spec/03_system/feature/usage/tuple_types_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/tuple_types_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/tuple_types_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/tuple_types_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates tuple literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/tuple_types_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gets tuple length' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/tuple_types_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accesses elements by index' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
