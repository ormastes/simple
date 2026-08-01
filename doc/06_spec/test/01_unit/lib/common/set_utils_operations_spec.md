# Set Utils Operations Specification

> <details>

<!-- sdn-diagram:id=set_utils_operations_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=set_utils_operations_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

set_utils_operations_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=set_utils_operations_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Set Utils Operations Specification

## Scenarios

### Set Utils Ext

#### keeps set construction and membership operations available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = set_source()

expect(source).to_contain("struct Set<T>:")
expect(source).to_contain("static fn new() -> Set<T>")
expect(source).to_contain("static fn from(items: [T]) -> Set<T>")
expect(source).to_contain("me insert(self, value: T) -> bool")
expect(source).to_contain("fn has(self, value: T) -> bool")
```

</details>

#### keeps set algebra operations and aliases available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = set_source()

expect(source).to_contain("fn union(self, other: Set<T>) -> Set<T>")
expect(source).to_contain("fn intersect(self, other: Set<T>) -> Set<T>")
expect(source).to_contain("fn intersection(self, other: Set<T>) -> Set<T>")
expect(source).to_contain("fn difference(self, other: Set<T>) -> Set<T>")
expect(source).to_contain("fn symmetric_difference(self, other: Set<T>) -> Set<T>")
```

</details>

#### keeps multi-set helper functions available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = set_source()

expect(source).to_contain("pub fn set_from_list<T>(items: [T]) -> Set<T>")
expect(source).to_contain("pub fn intersect_all<T>(sets: [Set<T>]) -> Set<T>")
expect(source).to_contain("pub fn union_all<T>(sets: [Set<T>]) -> Set<T>")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/set_utils_operations_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Set Utils Ext

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
