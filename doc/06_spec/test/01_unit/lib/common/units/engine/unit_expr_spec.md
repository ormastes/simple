# Unit Expr Specification

> <details>

<!-- sdn-diagram:id=unit_expr_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=unit_expr_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

unit_expr_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=unit_expr_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unit Expr Specification

## Scenarios

### World unit expression engine

#### parses km per hour exactly

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = parse_unit_expression("km/h")
expect(parsed.ok).to_equal(true)
expect(parsed.expression.scale.numerator).to_equal(5)
expect(parsed.expression.scale.denominator).to_equal(18)
expect(unit_expression_factor_exponent(parsed.expression, "metre")).to_equal(1)
expect(unit_expression_factor_exponent(parsed.expression, "second")).to_equal(-1)
```

</details>

#### accepts canonical aliases without changing canonical formatting

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = parse_unit_expression("kmph")
expect(parsed.ok).to_equal(true)
expect(format_unit_expression(parsed.expression)).to_equal("km/h")
```

</details>

#### parses chemistry concentration aliases

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = parse_unit_expression("M")
expect(parsed.ok).to_equal(true)
expect(parsed.expression.scale.numerator).to_equal(1000)
expect(unit_expression_factor_exponent(parsed.expression, "mole")).to_equal(1)
expect(unit_expression_factor_exponent(parsed.expression, "metre")).to_equal(-3)
expect(format_unit_expression(parsed.expression)).to_equal("mol/L")
```

</details>

#### reports unsupported expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = parse_unit_expression("USD/h")
expect(parsed.ok).to_equal(false)
expect(parsed.error).to_contain("unknown unit expression")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/units/engine/unit_expr_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- World unit expression engine

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
