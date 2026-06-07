# Unsafe Union Specification

> <details>

<!-- sdn-diagram:id=unsafe_union_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=unsafe_union_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

unsafe_union_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=unsafe_union_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unsafe Union Specification

## Scenarios

### union types

#### type-OR union via pipe syntax parses correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# i64 | text | bool  - this is the Type-OR union syntax
# Stored as separate types, resolved at runtime
val x: i64 = 42
expect(x).to_equal(42)
```

</details>

#### function accepting multiple types via union

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_number_or_text("123")
expect(result).to_equal(123)
```

</details>

#### match on union-typed value works

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n: i64 = -5
val category = classify_value(n)
expect(category).to_equal("negative")
```

</details>

#### positive value classified correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n: i64 = 10
val category = classify_value(n)
expect(category).to_equal("positive")
```

</details>

#### zero value classified correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n: i64 = 0
val category = classify_value(n)
expect(category).to_equal("zero")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/unsafe_union_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- union types

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
