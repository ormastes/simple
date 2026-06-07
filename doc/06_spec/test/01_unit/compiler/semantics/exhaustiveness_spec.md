# Exhaustiveness Specification

> <details>

<!-- sdn-diagram:id=exhaustiveness_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=exhaustiveness_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

exhaustiveness_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=exhaustiveness_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Exhaustiveness Specification

## Scenarios

### exhaustiveness checking

#### exhaustive match with wildcard succeeds

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
val result = match x:
    case 5: "five"
    case _: "other"
expect(result).to_equal("five")
```

</details>

#### match with all cases covered works

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val y = true
val result = match y:
    case true: "yes"
    case false: "no"
expect(result).to_equal("yes")
```

</details>

#### or-pattern covers multiple cases

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val z = 2
val result = match z:
    case 1 | 2 | 3: "small"
    case _: "big"
expect(result).to_equal("small")
```

</details>

#### match with nil coverage works

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = nil
val result = match opt:
    case nil: "none"
    case _: "some"
expect(result).to_equal("none")
```

</details>

#### guard prevents false match fallthrough

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = 10
val result = match n:
    case 10 if n > 100: "impossible"
    case _: "correct"
expect(result).to_equal("correct")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/exhaustiveness_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- exhaustiveness checking

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
