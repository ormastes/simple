# List Utils Specification

> Tests covering List Utilities, Reverse, Chunk, Interleave, Rotation, Deduplication, Flatten, Windows, Intersperse, Slicing, Comparison, Sorting Check.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# List Utils Specification

## Scenarios

### List Utilities

### Reverse

#### reverses list

- reverses list


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reverses list")
expect array_equals(array_reverse([1, 2, 3, 4]), [4, 3, 2, 1])
```

</details>

#### handles single element

- handles single element


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single element")
expect array_equals(array_reverse([1]), [1])
```

</details>

#### handles empty list

- handles empty list


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty list")
val empty: [i64] = []
expect array_reverse(empty).len() == 0
```

</details>

### Chunk

#### chunks list into parts

- chunks list into parts


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chunks list into parts")
val chunks_list = array_chunk([1, 2, 3, 4, 5], 2)
expect chunks_list.len() == 3
```

</details>

#### handles exact fit

- handles exact fit


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles exact fit")
val chunks_list = array_chunk([1, 2, 3, 4], 2)
expect chunks_list.len() == 2
```

</details>

#### handles size larger than list

- handles size larger than list


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles size larger than list")
val chunks_list = array_chunk([1, 2], 5)
expect chunks_list.len() == 1
```

</details>

### Interleave

#### interleaves equal length lists

- interleaves equal length lists


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interleaves equal length lists")
val result = array_interleave([1, 2, 3], [4, 5, 6])
expect array_equals(result, [1, 4, 2, 5, 3, 6])
```

</details>

#### handles different lengths

- handles different lengths


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles different lengths")
val result = array_interleave([1, 2], [3, 4, 5, 6])
expect result.len() == 6
```

</details>

### Rotation

#### rotates left

- rotates left


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rotates left")
expect array_equals(array_rotate_left([1, 2, 3, 4, 5], 2), [3, 4, 5, 1, 2])
```

</details>

#### rotates left by zero

- rotates left by zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rotates left by zero")
expect array_equals(array_rotate_left([1, 2, 3], 0), [1, 2, 3])
```

</details>

#### rotates right

- rotates right


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rotates right")
expect array_equals(array_rotate_right([1, 2, 3, 4, 5], 2), [4, 5, 1, 2, 3])
```

</details>

### Deduplication

#### removes consecutive duplicates

- removes consecutive duplicates


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes consecutive duplicates")
expect array_equals(array_dedup([1, 1, 2, 2, 3, 3]), [1, 2, 3])
```

</details>

#### keeps non-consecutive duplicates

- keeps non-consecutive duplicates


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps non-consecutive duplicates")
expect array_equals(array_dedup([1, 2, 1, 2]), [1, 2, 1, 2])
```

</details>

#### dedup_all removes all duplicates

- dedup_all removes all duplicates


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dedup_all removes all duplicates")
expect array_equals(array_dedup_all([1, 2, 1, 3, 2]), [1, 2, 3])
```

</details>

### Flatten

#### flattens nested lists

- flattens nested lists


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flattens nested lists")
val nested = [[1, 2], [3, 4], [5]]
expect array_equals(array_flatten(nested), [1, 2, 3, 4, 5])
```

</details>

#### handles empty nested list

- handles empty nested list


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty nested list")
val empty: [[i64]] = []
expect array_flatten(empty).len() == 0
```

</details>

### Windows

#### creates sliding windows

- creates sliding windows


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates sliding windows")
val wins = array_windows([1, 2, 3, 4], 2)
expect wins.len() == 3
```

</details>

#### handles size too large

- handles size too large


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles size too large")
val wins = array_windows([1, 2], 5)
expect wins.len() == 0
```

</details>

### Intersperse

#### inserts separator between elements

- inserts separator between elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inserts separator between elements")
expect array_equals(array_intersperse([1, 2, 3], 0), [1, 0, 2, 0, 3])
```

</details>

#### handles single element

- handles single element


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single element")
expect array_equals(array_intersperse([1], 0), [1])
```

</details>

### Slicing

#### take gets first n elements

- take gets first n elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("take gets first n elements")
expect array_equals(array_take([1, 2, 3, 4, 5], 3), [1, 2, 3])
```

</details>

#### take handles oversized n

- take handles oversized n


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("take handles oversized n")
expect array_equals(array_take([1, 2], 5), [1, 2])
```

</details>

#### drop removes first n elements

- drop removes first n elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("drop removes first n elements")
expect array_equals(array_drop([1, 2, 3, 4, 5], 2), [3, 4, 5])
```

</details>

#### drop handles oversized n

- drop handles oversized n


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("drop handles oversized n")
val dropped = array_drop([1, 2], 5)
expect dropped.len() == 0
```

</details>

### Comparison

#### list_equals returns true for equal

- list_equals returns true for equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("list_equals returns true for equal")
expect array_equals([1, 2, 3], [1, 2, 3])
```

</details>

#### list_equals returns false for different

- list_equals returns false for different


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("list_equals returns false for different")
expect not array_equals([1, 2], [1, 2, 3])
expect not array_equals([1, 2, 3], [1, 3, 2])
```

</details>

### Sorting Check

#### is_sorted detects sorted

- is_sorted detects sorted


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_sorted detects sorted")
expect array_is_sorted([1, 2, 3, 4])
```

</details>

#### is_sorted detects unsorted

- is_sorted detects unsorted


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_sorted detects unsorted")
expect not array_is_sorted([1, 3, 2, 4])
```

</details>

#### is_sorted handles empty

- is_sorted handles empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_sorted handles empty")
val empty: [i64] = []
expect array_is_sorted(empty)
```

</details>

#### is_sorted handles single element

- is_sorted handles single element


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_sorted handles single element")
expect array_is_sorted([1])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/list_utils_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering List Utilities, Reverse, Chunk, Interleave, Rotation, Deduplication, Flatten, Windows, Intersperse, Slicing, Comparison, Sorting Check.
- List Utilities
- Reverse
- Chunk
- Interleave
- Rotation
- Deduplication
- Flatten
- Windows
- Intersperse
- Slicing
- Comparison
- Sorting Check

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
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

- Canonical SPipe generation for source `c3f6fe40e4d6dd5d582c2bc0fdc868ace9f2f02baa13ef2e0c6d4302aa1d1d4d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c3f6fe40e4d6dd5d582c2bc0fdc868ace9f2f02baa13ef2e0c6d4302aa1d1d4d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c3f6fe40e4d6dd5d582c2bc0fdc868ace9f2f02baa13ef2e0c6d4302aa1d1d4d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/list_utils_spec.spl
mirror: doc/06_spec/unit/app/tooling/list_utils_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/list_utils_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/list_utils_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/list_utils_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reverses list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/list_utils_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles single element' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/list_utils_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles empty list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
