# Libc Stdlib Specification

> Tests covering SimpleOS libc stdlib (musl-shaped), libc_atol, libc_abs, libc_labs, libc_max, libc_min, libc_bsearch, libc_qsort.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Libc Stdlib Specification

## Scenarios

### SimpleOS libc stdlib (musl-shaped)

### libc_atol

#### parses simple decimal
#### parses negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_atol("-42".bytes())).to_equal(-42)
```

</details>

#### parses positive sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_atol("+42".bytes())).to_equal(42)
```

</details>

#### skips leading whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_atol("  42".bytes())).to_equal(42)
```

</details>

#### stops at non-digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_atol("42abc".bytes())).to_equal(42)
```

</details>

#### stops at non-digit after sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_atol("-42x".bytes())).to_equal(-42)
```

</details>

#### handles zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_atol("0".bytes())).to_equal(0)
```

</details>

#### handles large number

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_atol("1234567".bytes())).to_equal(1234567)
```

</details>

#### handles empty or non-numeric

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_atol("abc".bytes())).to_equal(0)
```

</details>

### libc_abs

#### returns positive unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_abs(42)).to_equal(42)
```

</details>

#### returns negative as positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_abs(-42)).to_equal(42)
```

</details>

#### handles zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_abs(0)).to_equal(0)
```

</details>

### libc_labs

#### returns positive unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_labs(42)).to_equal(42)
```

</details>

#### returns negative as positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_labs(-42)).to_equal(42)
```

</details>

#### handles zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_labs(0)).to_equal(0)
```

</details>

### libc_max

#### returns greater value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_max(10, 20)).to_equal(20)
```

</details>

#### returns greater when first is larger

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_max(30, 10)).to_equal(30)
```

</details>

#### handles equal values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_max(42, 42)).to_equal(42)
```

</details>

#### handles negatives

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_max(-10, -5)).to_equal(-5)
```

</details>

### libc_min

#### returns lesser value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_min(10, 20)).to_equal(10)
```

</details>

#### returns lesser when second is smaller

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_min(30, 10)).to_equal(10)
```

</details>

#### handles equal values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_min(42, 42)).to_equal(42)
```

</details>

#### handles negatives

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_min(-10, -5)).to_equal(-10)
```

</details>

### libc_bsearch

#### finds element at beginning

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3, 4, 5]
expect(libc_bsearch(arr, 1)).to_equal(0)
```

</details>

#### finds element in middle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3, 4, 5]
expect(libc_bsearch(arr, 3)).to_equal(2)
```

</details>

#### finds element at end

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3, 4, 5]
expect(libc_bsearch(arr, 5)).to_equal(4)
```

</details>

#### returns -1 when not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3, 4, 5]
expect(libc_bsearch(arr, 10)).to_equal(-1)
```

</details>

#### returns -1 for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [i64] = []
expect(libc_bsearch(arr, 5)).to_equal(-1)
```

</details>

#### finds in single element array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [42]
expect(libc_bsearch(arr, 42)).to_equal(0)
```

</details>

#### handles negative numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [-5, -2, 0, 3, 7]
expect(libc_bsearch(arr, -2)).to_equal(1)
```

</details>

### libc_qsort

#### sorts unsorted array

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [3, 1, 4, 1, 5]
val sorted = libc_qsort(arr)
expect(sorted.len()).to_equal(5)
expect(sorted[0]).to_equal(1)
expect(sorted[1]).to_equal(1)
expect(sorted[2]).to_equal(3)
expect(sorted[3]).to_equal(4)
expect(sorted[4]).to_equal(5)
```

</details>

#### handles array with negatives

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [3, -1, 0, -5, 2]
val sorted = libc_qsort(arr)
expect(sorted[0]).to_equal(-5)
expect(sorted[1]).to_equal(-1)
expect(sorted[2]).to_equal(0)
expect(sorted[3]).to_equal(2)
expect(sorted[4]).to_equal(3)
```

</details>

#### handles array with duplicates

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [5, 2, 5, 1, 2]
val sorted = libc_qsort(arr)
expect(sorted[0]).to_equal(1)
expect(sorted[1]).to_equal(2)
expect(sorted[2]).to_equal(2)
expect(sorted[3]).to_equal(5)
expect(sorted[4]).to_equal(5)
```

</details>

#### leaves original array unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [3, 1, 4, 1, 5]
val orig_first = arr[0]
val sorted = libc_qsort(arr)
expect(arr[0]).to_equal(orig_first)
expect(arr[0]).to_equal(3)
```

</details>

#### handles already sorted array

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3, 4, 5]
val sorted = libc_qsort(arr)
expect(sorted[0]).to_equal(1)
expect(sorted[4]).to_equal(5)
```

</details>

#### handles reverse sorted array

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [5, 4, 3, 2, 1]
val sorted = libc_qsort(arr)
expect(sorted[0]).to_equal(1)
expect(sorted[4]).to_equal(5)
```

</details>

#### handles single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [42]
val sorted = libc_qsort(arr)
expect(sorted[0]).to_equal(42)
```

</details>

#### handles empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [i64] = []
val sorted = libc_qsort(arr)
expect(sorted.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/libc/libc_stdlib_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS libc stdlib (musl-shaped), libc_atol, libc_abs, libc_labs, libc_max, libc_min, libc_bsearch, libc_qsort.
- SimpleOS libc stdlib (musl-shaped)
- libc_atol
- libc_abs
- libc_labs
- libc_max
- libc_min
- libc_bsearch
- libc_qsort

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
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

- Canonical SPipe generation for source `89551214d8d12b086e733bc0cbeae2629e3a5e4c129513c0fd43d8b16e1d1419`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `89551214d8d12b086e733bc0cbeae2629e3a5e4c129513c0fd43d8b16e1d1419`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `89551214d8d12b086e733bc0cbeae2629e3a5e4c129513c0fd43d8b16e1d1419`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **77/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/libc/libc_stdlib_spec.spl
mirror: doc/06_spec/01_unit/os/libc/libc_stdlib_spec.md (current)
findings: 9 blockers: 1
  narrative=100 structure=60 oracle=70
  traceability=60 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=77; blocker cap makes effective=49
doc/06_spec/01_unit/os/libc/libc_stdlib_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/libc/libc_stdlib_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/libc/libc_stdlib_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/os/libc/libc_stdlib_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 52 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/libc/libc_stdlib_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/libc/libc_stdlib_spec.spl:22:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'parses simple decimal' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/libc/libc_stdlib_spec.spl:27:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'parses negative' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/libc/libc_stdlib_spec.spl:30:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'parses positive sign' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/libc/libc_stdlib_spec.spl:33:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'skips leading whitespace' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
