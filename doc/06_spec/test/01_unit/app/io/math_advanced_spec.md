# Math Advanced Specification

> <details>

<!-- sdn-diagram:id=math_advanced_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=math_advanced_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

math_advanced_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=math_advanced_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Advanced Specification

## Scenarios

### app.io.math

### logarithms

#### math_log computes natural log

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_log(1.0)
expect(result).to_equal(0.0)
```

</details>

#### math_log10 computes base-10 log

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_log10(100.0)
expect(result).to_equal(2.0)
```

</details>

#### math_log2 computes base-2 log

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_log2(8.0)
expect(result).to_equal(3.0)
```

</details>

### inverse trig

#### math_asin of 0 is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_asin(0.0)
expect(result).to_equal(0.0)
```

</details>

#### math_acos of 1 is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_acos(1.0)
expect(result).to_equal(0.0)
```

</details>

#### math_atan of 0 is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_atan(0.0)
expect(result).to_equal(0.0)
```

</details>

#### math_atan2 computes angle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_atan2(0.0, 1.0)
expect(result).to_equal(0.0)
```

</details>

### hyperbolic

#### math_sinh of 0 is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_sinh(0.0)
expect(result).to_equal(0.0)
```

</details>

#### math_cosh of 0 is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_cosh(0.0)
expect(result).to_equal(1.0)
```

</details>

#### math_tanh of 0 is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = math_tanh(0.0)
expect(result).to_equal(0.0)
```

</details>

### rounding

#### math_ceil rounds up

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_ceil(2.3)).to_equal(3.0)
expect(math_ceil(2.0)).to_equal(2.0)
expect(math_ceil(-2.3)).to_equal(-2.0)
```

</details>

#### math_floor rounds down

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_floor(2.7)).to_equal(2.0)
expect(math_floor(2.0)).to_equal(2.0)
expect(math_floor(-2.3)).to_equal(-3.0)
```

</details>

#### math_round rounds to nearest

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(math_round(2.3)).to_equal(2.0)
expect(math_round(2.7)).to_equal(3.0)
expect(math_round(2.5)).to_equal(3.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/io/math_advanced_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- app.io.math
- logarithms
- inverse trig
- hyperbolic
- rounding

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
