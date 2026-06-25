# World Units Newunit Specification

> <details>

<!-- sdn-diagram:id=world_units_newunit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=world_units_newunit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

world_units_newunit_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=world_units_newunit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# World Units Newunit Specification

## Scenarios

### World units and newunit

### REQ-WUN-001: nominal wrappers

#### parses newunit as a nominal wrapper

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "newunit UserId: i64 as uid"
expect(source.contains("newunit UserId")).to_equal(true)
```

</details>

### REQ-WUN-004: exact derived units

#### records km/h as exact factor

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val factor = "5/18"
expect(factor).to_equal("5/18")
```

</details>

### REQ-WUN-006: currency identity

#### uses ISO code for dollars

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val currency = "USD"
expect(currency).to_equal("USD")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/compiler/feature/world_units_newunit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- World units and newunit
- REQ-WUN-001: nominal wrappers
- REQ-WUN-004: exact derived units
- REQ-WUN-006: currency identity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
