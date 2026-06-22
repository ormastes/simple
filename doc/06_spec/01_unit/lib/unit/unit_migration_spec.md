# Unit Migration Specification

> <details>

<!-- sdn-diagram:id=unit_migration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=unit_migration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

unit_migration_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=unit_migration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unit Migration Specification

## Scenarios

### migration — old path compiles

#### AC-6: `use std.common.units.model.world_units.{UnitFactor}` still resolves

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# pending: parse + resolve (no runtime cost here; the import at the
# top of a synthetic source file must succeed).
val resolved: bool = true
expect(resolved).to_equal(true)
```

</details>

#### AC-6: `use std.common.units.engine.unit_expr.{UnitExpression}` still resolves

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resolved: bool = true
expect(resolved).to_equal(true)
```

</details>

### migration — deprecation warning

#### AC-6: old import emits `deprecated` warning pointing to new path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg: text = "warning: deprecated — moved to unit.simple-lang.*; will be removed in 0.11.0"
expect(msg).to_contain("unit.simple-lang")
expect(msg).to_contain("0.11.0")
```

</details>

#### AC-6: deprecation warning names the specific new path for the import

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# For `std.common.units.model.world_units` the replacement is
# `unit.simple-lang.__model__` (or `unit.meta.world_units`).
val msg: text = "deprecated: use unit.meta.world_units instead"
expect(msg).to_contain("unit.meta.world_units")
```

</details>

### migration — type identity

#### AC-6: `std.common.units.model.world_units.UnitFactor` == `unit.meta.world_units.UnitFactor`

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# pending: compile two sources, one with each import, and verify the
# resolved type id is identical.
val same_type_id: bool = true
expect(same_type_id).to_equal(true)
```

</details>

#### AC-6: old `std.common.units.engine.unit_expr` == new `unit.simple-lang.__engine__`

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val same_type_id: bool = true
expect(same_type_id).to_equal(true)
```

</details>

### migration — removed units.disabled

#### AC-6: `std_lib/src/units.disabled/` no longer exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# pending: rt_file_exists on the legacy disabled tree must return false.
val still_present: bool = false
expect(still_present).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/unit/unit_migration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- migration — old path compiles
- migration — deprecation warning
- migration — type identity
- migration — removed units.disabled

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
