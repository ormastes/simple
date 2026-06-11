# World Units Specification

> <details>

<!-- sdn-diagram:id=world_units_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=world_units_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

world_units_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=world_units_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# World Units Specification

## Scenarios

### World unit model

#### keeps km/h conversion exact

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val factor = kilometre_per_hour_factor_to_metre_per_second()
expect(factor.numerator).to_equal(5)
expect(factor.denominator).to_equal(18)
```

</details>

#### blocks prefixes for accepted non-SI time and calendar units

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_prefix_blocked("h")).to_equal(true)
expect(is_prefix_blocked("d")).to_equal(true)
expect(is_prefix_blocked("a_g")).to_equal(true)
expect(is_prefix_blocked("m")).to_equal(false)
```

</details>

#### constructs exact ratios

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ratio = exact_ratio(1024, 1)
expect(ratio.numerator).to_equal(1024)
expect(ratio.denominator).to_equal(1)
```

</details>

#### normalizes exact ratios

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ratio = exact_ratio_normalize(exact_ratio(10, -20))
expect(ratio.numerator).to_equal(-1)
expect(ratio.denominator).to_equal(2)
```

</details>

#### multiplies and divides exact ratios

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val multiplied = exact_ratio_mul(exact_ratio(2, 3), exact_ratio(9, 4))
val divided = exact_ratio_div(exact_ratio(5, 18), exact_ratio(10, 3))
expect(multiplied.numerator).to_equal(3)
expect(multiplied.denominator).to_equal(2)
expect(divided.numerator).to_equal(1)
expect(divided.denominator).to_equal(12)
```

</details>

#### normalizes derived unit expressions exactly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expression = kilometre_per_hour_expression()
expect(expression.scale.numerator).to_equal(5)
expect(expression.scale.denominator).to_equal(18)
expect(unit_expression_factor_exponent(expression, "metre")).to_equal(1)
expect(unit_expression_factor_exponent(expression, "second")).to_equal(-1)
```

</details>

#### cancels matching unit factors

1. unit expression mul
2. unit expression from base
   - Expected: unit_expression_factor_count(expression) equals `1`
   - Expected: unit_expression_factor_exponent(expression, "second") equals `1`
   - Expected: unit_expression_factor_exponent(expression, "metre") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expression = unit_expression_div(
    unit_expression_mul(unit_expression_from_base("metre"), unit_expression_from_base("second")),
    unit_expression_from_base("metre")
)
expect(unit_expression_factor_count(expression)).to_equal(1)
expect(unit_expression_factor_exponent(expression, "second")).to_equal(1)
expect(unit_expression_factor_exponent(expression, "metre")).to_equal(0)
```

</details>

#### represents amount concentration through litre composition

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expression = mole_per_litre_expression()
expect(expression.scale.numerator).to_equal(1000)
expect(expression.scale.denominator).to_equal(1)
expect(unit_expression_factor_exponent(expression, "mole")).to_equal(1)
expect(unit_expression_factor_exponent(expression, "metre")).to_equal(-3)
```

</details>

#### pins required catalog identities

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val catalog = file_read("src/lib/common/units/catalog/world_units_v1.sdn")
expect(catalog_has_required_world_units(catalog)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/units/world_units_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- World unit model

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
