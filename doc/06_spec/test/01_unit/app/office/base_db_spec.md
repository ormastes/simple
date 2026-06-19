# base_db_spec

> Verifies the Base database component: an in-memory text table with row insertion, checked insertion, exact-match filtering (`select_where`), filtered counting, update/delete by predicate, and column projection (`project_column`). Inner-row cells are read via iteration to avoid the interpreter's `.get(>=1)` array-element corruption, so filtering by a non-first column works correctly.

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
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# base_db_spec

Verifies the Base database component: an in-memory text table with row insertion, checked insertion, exact-match filtering (`select_where`), filtered counting, update/delete by predicate, and column projection (`project_column`). Inner-row cells are read via iteration to avoid the interpreter's `.get(>=1)` array-element corruption, so filtering by a non-first column works correctly.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/base_db.md |
| Plan | doc/03_plan/sys_test/base_db.md |
| Design | doc/07_guide/app/ide_office_plugin_suite.md |
| Research | N/A |
| Source | `test/01_unit/app/office/base_db_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the Base database component: an in-memory text table with row
insertion, checked insertion, exact-match filtering (`select_where`), filtered
counting, update/delete by predicate, and column projection (`project_column`).
Inner-row cells are read via iteration to avoid the
interpreter's `.get(>=1)` array-element corruption, so filtering by a non-first
column works correctly.

## Examples

`insert_row_checked(table, ["1", "open"])` appends a row only when the row width
matches the table schema. `update_where(table, "status", "open", "status",
"done")` updates every matching row through an immutable result wrapper, and
`delete_where(table, "status", "done")` returns a new table with those rows
removed.

**Requirements:** doc/02_requirements/feature/base_db.md
**NFR:** doc/02_requirements/nfr/base_db.md
**Plan:** doc/03_plan/sys_test/base_db.md
**Design:** doc/07_guide/app/ide_office_plugin_suite.md
**Research:** N/A

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

#### counts rows by exact match

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _sample()
expect(count_where(t, "type", "melee")).to_equal(2)
expect(count_where(t, "type", "missing")).to_equal(0)
expect(count_where(t, "nope", "melee")).to_equal(0)
```

</details>

### Base table: checked edits
_Checked Base edits preserve table invariants and reject no-op predicates._

#### accepts checked inserts with matching schema width

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = new_table("tasks", ["id", "status"])
val result = insert_row_checked(t, ["1", "open"])
expect(result.accepted).to_be(true)
expect(result.reason).to_equal("inserted")
expect(result.affected_count).to_equal(1)
expect(row_count(result.table)).to_equal(1)
expect(row_count(t)).to_equal(0)
```

</details>

#### rejects short and long checked inserts without changing the table

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = new_table("tasks", ["id", "status"])
val short_row = insert_row_checked(t, ["1"])
val long_row = insert_row_checked(t, ["1", "open", "extra"])
expect(short_row.accepted).to_be(false)
expect(short_row.reason).to_equal("row-width-mismatch")
expect(short_row.affected_count).to_equal(0)
expect(row_count(short_row.table)).to_equal(0)
expect(long_row.accepted).to_be(false)
expect(long_row.reason).to_equal("row-width-mismatch")
expect(row_count(long_row.table)).to_equal(0)
```

</details>

#### updates matching rows by a non-first column predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _sample()
val result = update_where(t, "type", "melee", "type", "frontline")
expect(result.accepted).to_be(true)
expect(result.reason).to_equal("updated")
expect(result.affected_count).to_equal(2)
expect(count_where(result.table, "type", "frontline")).to_equal(2)
expect(count_where(t, "type", "melee")).to_equal(2)
```

</details>

#### deletes matching rows by a non-first column predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _sample()
val result = delete_where(t, "type", "melee")
expect(result.accepted).to_be(true)
expect(result.reason).to_equal("deleted")
expect(result.affected_count).to_equal(2)
expect(row_count(result.table)).to_equal(1)
expect(project_column(result.table, "name")).to_contain("beta")
expect(row_count(t)).to_equal(3)
```

</details>

#### rejects missing columns and no-match edits without changing the table

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _sample()
val missing_match = update_where(t, "missing", "melee", "type", "frontline")
val missing_update = update_where(t, "type", "melee", "missing", "frontline")
val no_update = update_where(t, "type", "flying", "type", "air")
val no_delete = delete_where(t, "type", "flying")
expect(missing_match.reason).to_equal("missing-match-column")
expect(missing_update.reason).to_equal("missing-update-column")
expect(no_update.reason).to_equal("no-matching-rows")
expect(no_delete.reason).to_equal("no-matching-rows")
expect(row_count(missing_match.table)).to_equal(3)
expect(row_count(missing_update.table)).to_equal(3)
expect(row_count(no_update.table)).to_equal(3)
expect(row_count(no_delete.table)).to_equal(3)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/base_db.md](doc/02_requirements/feature/base_db.md)
- **Plan:** [doc/03_plan/sys_test/base_db.md](doc/03_plan/sys_test/base_db.md)
- **Design:** [doc/07_guide/app/ide_office_plugin_suite.md](doc/07_guide/app/ide_office_plugin_suite.md)


</details>
