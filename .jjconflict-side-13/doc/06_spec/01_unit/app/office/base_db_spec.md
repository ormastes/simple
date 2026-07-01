# Base Db Specification

> _A table accumulates rows and resolves column indices._

<!-- sdn-diagram:id=base_db_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=base_db_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

base_db_spec -> std
base_db_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=base_db_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Base Db Specification

## Scenarios

### Base table: rows and columns
_A table accumulates rows and resolves column indices._

#### counts inserted rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _sample()
expect(row_count(t)).to_equal(3)
```

</details>

#### resolves a non-first column index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _sample()
expect(column_index(t, "type")).to_equal(1)
```

</details>

#### returns -1 for an unknown column

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _sample()
expect(column_index(t, "nope")).to_equal(0 - 1)
```

</details>

### Base table: query
_Filtering and projection read non-first columns correctly._

#### filters rows by a non-first column value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _sample()
val melee = select_where(t, "type", "melee")
expect(melee.len()).to_equal(2)
```

</details>

#### filters a single match

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _sample()
val ranged = select_where(t, "type", "ranged")
expect(ranged.len()).to_equal(1)
```

</details>

#### projects a non-first column

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _sample()
val types = project_column(t, "type")
expect(types.len()).to_equal(3)
expect(types).to_contain("ranged")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/base_db_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Base table: rows and columns
- Base table: query

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
