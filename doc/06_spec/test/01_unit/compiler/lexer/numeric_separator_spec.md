# Numeric Separator Specification

> <details>

<!-- sdn-diagram:id=numeric_separator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=numeric_separator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

numeric_separator_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=numeric_separator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Numeric Separator Specification

## Scenarios

### numeric separators

#### underscore in decimal integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = 1_000_000
expect(n).to_equal(1000000)
```

</details>

#### underscore in smaller number

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = 1_234
expect(n).to_equal(1234)
```

</details>

#### hex literal with underscore

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = 0xFF_FF
expect(n).to_equal(65535)
```

</details>

#### binary literal with underscore

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = 0b1111_0000
expect(n).to_equal(240)
```

</details>

#### float with underscore

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = 3.141_592
expect(f).to_equal(3.141592)
```

</details>

#### multiple underscores work

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = 1_000_000_000
expect(n).to_equal(1000000000)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lexer/numeric_separator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- numeric separators

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
