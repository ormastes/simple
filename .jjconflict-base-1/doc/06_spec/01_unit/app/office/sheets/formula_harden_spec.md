# Formula Harden Specification

> <details>

<!-- sdn-diagram:id=formula_harden_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=formula_harden_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

formula_harden_spec -> std
formula_harden_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=formula_harden_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Formula Harden Specification

## Scenarios

### formula engine: cycle detection terminates

#### a self-referential formula returns an empty display instead of overflowing

- var sheet = Sheet new
- sheet set value
   - Expected: evaluate_formula_display_text("=C1", sheet) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("C1", "=C1+1")
expect(evaluate_formula_display_text("=C1", sheet)).to_equal("")
```

</details>

#### mutually-circular references terminate

- var sheet = Sheet new
- sheet set value
- sheet set value
   - Expected: evaluate_formula_display_text("=A1", sheet) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
sheet.set_value("A1", "=B1")
sheet.set_value("B1", "=A1")
expect(evaluate_formula_display_text("=A1", sheet)).to_equal("")
```

</details>

#### an empty formula yields an empty display

- var sheet = Sheet new
   - Expected: evaluate_formula_display_text("=", sheet) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sheet = Sheet.new("S1")
expect(evaluate_formula_display_text("=", sheet)).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_harden_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- formula engine: cycle detection terminates

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
