# Union Type Specification

> <details>

<!-- sdn-diagram:id=union_type_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=union_type_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

union_type_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=union_type_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Union Type Specification

## Scenarios

### union types A | B

#### function works with integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = accepts_value(42)
expect(result).to_equal("nonzero")
```

</details>

#### function works with zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = accepts_value(0)
expect(result).to_equal("zero")
```

</details>

#### nullable with nil coalescing operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: i64 = 0
val result = x ?? 42
expect(result).to_equal(0)
```

</details>

#### nullable type with real value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = nullable_int(99)
expect(result).to_equal(99)
```

</details>

#### match on typed value works

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = "world"
val result = match x:
    case "world": "matched string"
    case _: "other"
expect(result).to_equal("matched string")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/union_type_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- union types A | B

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
