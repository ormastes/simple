# Where Clause Specification

> <details>

<!-- sdn-diagram:id=where_clause_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=where_clause_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

where_clause_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=where_clause_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Where Clause Specification

## Scenarios

### where clause constraints

#### identity function works

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = identity(42)
expect(result).to_equal(42)
```

</details>

#### identity works with text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = identity("hello")
expect(result).to_equal("hello")
```

</details>

#### max_val with constraints

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = max_val(3, 7)
expect(result).to_equal(7)
```

</details>

#### max_text with string comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = max_text("apple", "banana")
expect(result).to_equal("banana")
```

</details>

#### clamp within range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = clamp(5, 0, 10)
expect(result).to_equal(5)
```

</details>

#### clamp above range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = clamp(15, 0, 10)
expect(result).to_equal(10)
```

</details>

#### clamp below range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = clamp(-5, 0, 10)
expect(result).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/where_clause_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- where clause constraints

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
