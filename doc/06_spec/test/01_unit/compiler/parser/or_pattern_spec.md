# Or Pattern Specification

> <details>

<!-- sdn-diagram:id=or_pattern_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=or_pattern_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

or_pattern_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=or_pattern_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Or Pattern Specification

## Scenarios

### or-patterns in match

#### matches first alternative

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1
val result = match x:
    case 1 | 2 | 3: "small"
    case _: "other"
expect(result).to_equal("small")
```

</details>

#### matches second alternative

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 2
val result = match x:
    case 1 | 2 | 3: "small"
    case _: "other"
expect(result).to_equal("small")
```

</details>

#### matches third alternative

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 3
val result = match x:
    case 1 | 2 | 3: "small"
    case _: "other"
expect(result).to_equal("small")
```

</details>

#### falls through to wildcard when no alternative matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 99
val result = match x:
    case 1 | 2 | 3: "small"
    case _: "other"
expect(result).to_equal("other")
```

</details>

#### or-pattern on text

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "yes"
val result = match s:
    case "yes" | "y" | "true": "affirmative"
    case "no" | "n" | "false": "negative"
    case _: "unknown"
expect(result).to_equal("affirmative")
```

</details>

#### or-pattern on text second branch

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "n"
val result = match s:
    case "yes" | "y" | "true": "affirmative"
    case "no" | "n" | "false": "negative"
    case _: "unknown"
expect(result).to_equal("negative")
```

</details>

#### two-way or-pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = 7
val result = match n:
    case 7 | 42: "magic"
    case _: "mundane"
expect(result).to_equal("magic")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/or_pattern_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- or-patterns in match

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
