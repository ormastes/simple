# Math Specification

> <details>

<!-- sdn-diagram:id=math_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=math_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

math_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=math_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Specification

## Scenarios

### std.math.math (transcendental SFFI wrappers)

#### math_sqrt

#### sqrt of 4 is 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = math_sqrt(4.0)
expect res == 2.0
```

</details>

#### sqrt of 1 is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = math_sqrt(1.0)
expect res == 1.0
```

</details>

#### sqrt of 0 is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = math_sqrt(0.0)
expect res == 0.0
```

</details>

#### math_pow

#### 2 raised to 3 is 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = math_pow(2.0, 3.0)
expect res == 8.0
```

</details>

#### anything to power 0 is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = math_pow(5.0, 0.0)
expect res == 1.0
```

</details>

#### math_abs

#### abs of negative is positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = math_abs(-3.5)
expect res == 3.5
```

</details>

#### abs of positive is unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = math_abs(3.5)
expect res == 3.5
```

</details>

#### abs of zero is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = math_abs(0.0)
expect res == 0.0
```

</details>

#### math_trunc

#### truncates positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = math_trunc(3.9)
expect res == 3.0
```

</details>

#### truncates negative toward zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = math_trunc(-3.9)
expect res == -3.0
```

</details>

#### math_round

#### rounds half up

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = math_round(2.5)
expect res == 3.0
```

</details>

#### rounds down when below half

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = math_round(2.4)
expect res == 2.0
```

</details>

#### rounds negative half away from zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = math_round(-2.5)
expect res == -3.0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/math/math_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- std.math.math (transcendental SFFI wrappers)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
