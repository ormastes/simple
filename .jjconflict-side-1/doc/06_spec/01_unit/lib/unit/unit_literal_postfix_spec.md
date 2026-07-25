# Unit Literal Postfix Specification

> <details>

<!-- sdn-diagram:id=unit_literal_postfix_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=unit_literal_postfix_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

unit_literal_postfix_spec -> std
unit_literal_postfix_spec -> unit
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=unit_literal_postfix_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unit Literal Postfix Specification

## Scenarios

### unit postfix lexer — integer

#### AC-3: 10_km parses as km-typed integer literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d: km = 10_km
expect(d.value()).to_equal(10)
```

</details>

#### AC-3: 0_x parses as ui x-axis unit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p: x = 0_x
expect(p.value()).to_equal(0)
```

</details>

#### AC-3: 1_w parses as ui width unit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val width: w = 1_w
expect(width.value()).to_equal(1)
```

</details>

#### AC-3: -5_degC parses as signed temperature literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t: degC = -5_degC
expect(t.value()).to_equal(-5)
```

</details>

### unit postfix lexer — float

#### AC-3: 3.14_rad parses as rad-typed float literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a: rad = 3.14_rad
expect(a.value()).to_be_greater_than(3)
```

</details>

#### AC-3: 60_kmph parses as composite-unit literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v: kmph = 60_kmph
expect(v.value()).to_equal(60)
```

</details>

### digit separator vs unit postfix

#### AC-3: 10_000_km lexes as 10000 km (separator, not suffix _000_km)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d: km = 10_000_km
expect(d.value()).to_equal(10000)
```

</details>

#### AC-3: 1_000_000_m yields one million metres

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d: m = 1_000_000_m
expect(d.value()).to_equal(1000000)
```

</details>

### no suffix — plain primitive

#### AC-3: 42 without suffix stays a plain i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n: i64 = 42
expect(n).to_equal(42)
```

</details>

#### AC-3: 3.14 without suffix stays a plain f64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: f64 = 3.14
expect(x).to_be_greater_than(3)
```

</details>

### unknown suffix

#### AC-3: 42_xyzzy reports unknown-unit error with suggestion

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# pending: compiler_diagnostic_for_source("val n = 42_xyzzy").code
val expected_code: text = "E_UNIT_UNKNOWN_SUFFIX"
expect(expected_code).to_equal("E_UNIT_UNKNOWN_SUFFIX")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/unit/unit_literal_postfix_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- unit postfix lexer — integer
- unit postfix lexer — float
- digit separator vs unit postfix
- no suffix — plain primitive
- unknown suffix

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
