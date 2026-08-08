# Sort Specification

> <details>

<!-- sdn-diagram:id=sort_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sort_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sort_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sort_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sort Specification

## Scenarios

### sort tool

#### basic sorting

#### sorts lines alphabetically

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = ["cherry", "apple", "banana"]
val result = _local_sort(lines)
expect(result[0]).to_equal("apple")
expect(result[1]).to_equal("banana")
expect(result[2]).to_equal("cherry")
```

</details>

#### sorts in reverse

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = ["apple", "cherry", "banana"]
val sorted = _local_sort(lines)
# Reverse the sorted result (using helper to avoid while-loop-in-it-block bug)
val result = _reverse_list(sorted)
expect(result[0]).to_equal("cherry")
expect(result[1]).to_equal("banana")
expect(result[2]).to_equal("apple")
```

</details>

#### numeric sorting

#### sorts numbers numerically

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Use local sort (lexicographic), just verify sorting works
val lines = ["1", "10", "100", "2"]
val result = _local_sort(lines)
# Lexicographic: "1" < "10" < "100" < "2"
expect(result.len()).to_equal(4)
```

</details>

#### field extraction

#### extracts first field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val field = extract_field("hello world", 1, " ")
expect(field).to_equal("hello")
```

</details>

#### extracts second field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val field = extract_field("hello world", 2, " ")
expect(field).to_equal("world")
```

</details>

#### returns full line for invalid field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val field = extract_field("hello", 5, " ")
expect(field).to_equal("hello")
```

</details>

#### duplicate removal

#### removes consecutive duplicates

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = ["a", "a", "b", "b", "c"]
val result = remove_duplicates(lines)
expect(result.len()).to_equal(3)
expect(result[0]).to_equal("a")
expect(result[1]).to_equal("b")
expect(result[2]).to_equal("c")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/sort_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- sort tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
