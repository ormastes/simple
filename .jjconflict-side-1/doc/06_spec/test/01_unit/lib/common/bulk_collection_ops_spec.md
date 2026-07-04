# Bulk Collection Ops Specification

> <details>

<!-- sdn-diagram:id=bulk_collection_ops_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bulk_collection_ops_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bulk_collection_ops_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bulk_collection_ops_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bulk Collection Ops Specification

## Scenarios

### map_join

#### maps and joins with separator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = map_join([1, 2, 3], "{_1}", ", ")
expect(result).to_equal("1, 2, 3")
```

</details>

#### handles empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = map_join([], "{_1}", ", ")
expect(result).to_equal("")
```

</details>

#### handles single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = map_join([42], "num={_1}", ", ")
expect(result).to_equal("num=42")
```

</details>

#### works with transform function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = map_join([1, 2, 3], \x: "{x * 10}", "-")
expect(result).to_equal("10-20-30")
```

</details>

### filter_map_join

#### filters then maps then joins

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = filter_map_join([1, 2, 3, 4, 5], _1 > 2, "{_1}", ", ")
expect(result).to_equal("3, 4, 5")
```

</details>

#### handles all filtered out

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = filter_map_join([1, 2, 3], _1 > 10, "{_1}", ", ")
expect(result).to_equal("")
```

</details>

#### handles none filtered out

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = filter_map_join([1, 2], _1 > 0, "v{_1}", "+")
expect(result).to_equal("v1+v2")
```

</details>

### map_to_text

#### maps and concatenates without separator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = map_to_text([1, 2, 3], "{_1}")
expect(result).to_equal("123")
```

</details>

#### handles empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = map_to_text([], "{_1}")
expect(result).to_equal("")
```

</details>

#### works with text transform

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = map_to_text(["a", "b", "c"], "[{_1}]")
expect(result).to_equal("[a][b][c]")
```

</details>

### enumerate_join

#### provides element and index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = enumerate_join(["a", "b", "c"], \elem, i: "{i}:{elem}", ", ")
expect(result).to_equal("0:a, 1:b, 2:c")
```

</details>

#### handles empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = enumerate_join([], \elem, i: "{i}:{elem}", ", ")
expect(result).to_equal("")
```

</details>

#### handles single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = enumerate_join(["only"], \elem, i: "{i}={elem}", ", ")
expect(result).to_equal("0=only")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/bulk_collection_ops_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- map_join
- filter_map_join
- map_to_text
- enumerate_join

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
