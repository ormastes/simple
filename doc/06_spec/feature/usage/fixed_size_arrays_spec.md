# Fixed-Size Array Types

> Fixed-size arrays use the `[T; N]` syntax to declare arrays whose length is known at declaration time and enforced at runtime. Unlike dynamic arrays, fixed-size arrays carry their size as part of the type annotation, enabling stronger guarantees about buffer lengths. This spec validates creation, indexing (including negative indices), read operations like `first()`/`last()`/`contains()`, iteration with `for`, and functional methods (`map`, `filter`, `reduce`) that return dynamic arrays.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fixed-Size Array Types

Fixed-size arrays use the `[T; N]` syntax to declare arrays whose length is known at declaration time and enforced at runtime. Unlike dynamic arrays, fixed-size arrays carry their size as part of the type annotation, enabling stronger guarantees about buffer lengths. This spec validates creation, indexing (including negative indices), read operations like `first()`/`last()`/`contains()`, iteration with `for`, and functional methods (`map`, `filter`, `reduce`) that return dynamic arrays.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LANG-008 |
| Category | Language |
| Status | Active |
| Source | `test/feature/usage/fixed_size_arrays_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Fixed-size arrays use the `[T; N]` syntax to declare arrays whose length is known at
declaration time and enforced at runtime. Unlike dynamic arrays, fixed-size arrays carry
their size as part of the type annotation, enabling stronger guarantees about buffer
lengths. This spec validates creation, indexing (including negative indices), read
operations like `first()`/`last()`/`contains()`, iteration with `for`, and functional
methods (`map`, `filter`, `reduce`) that return dynamic arrays.

## Syntax

```simple
use std.spec.step

val vec3: [f64; 3] = [1.0, 2.0, 3.0]
val arr: [i64; 5] = [1, 2, 3, 4, 5]
expect arr[-1] == 5
val doubled = vec3.map(_1 * 2)
val sum = arr.reduce(0, \acc, x: acc + x)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| `[T; N]` Syntax | Declares a fixed-size array of type T with exactly N elements |
| Runtime Size Check | Array size is validated at creation to match the declared N |
| Negative Indexing | `arr[-1]` accesses the last element, `arr[-2]` the second-to-last |
| Functional Methods | `map`, `filter`, `reduce` work on fixed arrays but return dynamic arrays |

## Scenarios

### Fixed-Size Arrays

#### Basic Syntax

#### creates fixed-size array with type annotation

- creates fixed-size array with type annotation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates fixed-size array with type annotation")
val vec3: [f64; 3] = [1.0, 2.0, 3.0]
expect vec3.len() == 3
```

</details>

#### creates fixed-size int array

- creates fixed-size int array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates fixed-size int array")
val arr: [i64; 5] = [1, 2, 3, 4, 5]
expect arr.len() == 5
```

</details>

#### creates single element fixed-size array

- creates single element fixed-size array


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates single element fixed-size array")
val arr: [i64; 1] = [42]
expect arr[0] == 42
expect arr.len() == 1
```

</details>

#### Indexing

#### allows indexing read

- allows indexing read


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows indexing read")
val vec3: [f64; 3] = [1.0, 2.0, 3.0]
expect vec3[0] == 1.0
expect vec3[1] == 2.0
expect vec3[2] == 3.0
```

</details>

#### allows negative indexing

- allows negative indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows negative indexing")
val arr: [i64; 3] = [10, 20, 30]
expect arr[-1] == 30
expect arr[-2] == 20
expect arr[-3] == 10
```

</details>

#### Read Operations

#### allows len

- allows len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows len")
val vec3: [f64; 3] = [1.0, 2.0, 3.0]
expect vec3.len() == 3
```

</details>

#### allows first and last

- allows first and last


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows first and last")
val arr: [i64; 4] = [10, 20, 30, 40]
expect arr.first() == 10
expect arr.last() == 40
```

</details>

#### allows contains

- allows contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows contains")
val arr: [i64; 3] = [1, 2, 3]
expect arr.contains(2)
expect not arr.contains(5)
```

</details>

#### allows iteration

- allows iteration


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows iteration")
val vec3: [i64; 3] = [1, 2, 3]
var sum = 0
for x in vec3:
    sum = sum + x
expect sum == 6
```

</details>

#### Functional Operations

#### allows map (returns dynamic array)

- allows map (returns dynamic array)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows map (returns dynamic array)")
val vec3: [i64; 3] = [1, 2, 3]
val doubled = vec3.map(_ * 2)
expect doubled[0] == 2
expect doubled[1] == 4
expect doubled[2] == 6
```

</details>

#### allows filter (returns dynamic array)

- allows filter (returns dynamic array)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows filter (returns dynamic array)")
val arr: [i64; 5] = [1, 2, 3, 4, 5]
val evens = arr.filter(_ % 2 == 0)
expect evens[0] == 2
expect evens.len() == 2
```

</details>

#### allows reduce

- allows reduce


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows reduce")
val arr: [i64; 4] = [1, 2, 3, 4]
val sum = arr.reduce(0, \acc, x: acc + x)
expect sum == 10
```

</details>

#### Display Format

#### displays with size annotation

- displays with size annotation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("displays with size annotation")
val vec3: [i64; 3] = [1, 2, 3]
# FixedSizeArray displays as [items; size]
expect vec3.len() == 3
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `132cf1cf1a0ef93cd4a4518debb881ed762b7ef9dd7e88e7ca63f8c97ec76fe9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `132cf1cf1a0ef93cd4a4518debb881ed762b7ef9dd7e88e7ca63f8c97ec76fe9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `132cf1cf1a0ef93cd4a4518debb881ed762b7ef9dd7e88e7ca63f8c97ec76fe9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/fixed_size_arrays_spec.spl
mirror: doc/06_spec/feature/usage/fixed_size_arrays_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/fixed_size_arrays_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/fixed_size_arrays_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/fixed_size_arrays_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates fixed-size array with type annotation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/fixed_size_arrays_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates fixed-size int array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/fixed_size_arrays_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates single element fixed-size array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
