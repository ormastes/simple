# Comprehension Specification

> <details>

<!-- sdn-diagram:id=comprehension_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=comprehension_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

comprehension_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=comprehension_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Comprehension Specification

## Scenarios

### List comprehension

#### for-first basic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = [for x in [1, 2, 3]: x * 2]
expect(result).to_equal([2, 4, 6])
```

</details>

#### for-first with filter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = [for x in [1, 2, 3, 4, 5] if x > 3: x]
expect(result).to_equal([4, 5])
```

</details>

#### for-first with range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = [for i in 0..5: i * i]
expect(result).to_equal([0, 1, 4, 9, 16])
```

</details>

#### for-first with range and filter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = [for i in 0..10 if i % 2 == 0: i]
expect(result).to_equal([0, 2, 4, 6, 8])
```

</details>

#### for-last basic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = [x * 2 for x in [1, 2, 3]]
expect(result).to_equal([2, 4, 6])
```

</details>

#### for-last with filter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = [x for x in [1, 2, 3, 4, 5] if x > 3]
expect(result).to_equal([4, 5])
```

</details>

#### empty result from filter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = [for x in [1, 2, 3] if x > 10: x]
expect(result).to_equal([])
```

</details>

#### empty source array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var empty: [i64] = []
val result = [for x in empty: x * 2]
expect(result).to_equal([])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/parser/comprehension_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- List comprehension

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
