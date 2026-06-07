# Sql Init Facade Specification

> 1. var query = SelectQuery from

<!-- sdn-diagram:id=sql_init_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sql_init_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sql_init_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sql_init_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sql Init Facade Specification

## Scenarios

### gc_async_mut database SQL package facade

#### re-exports canonical SQL package symbols

1. var query = SelectQuery from
2. query = query order
   - Expected: quote_ident("events") equals `"events"`
   - Expected: schema.columns.len() equals `1`
   - Expected: value.db_type() equals `DbType.Integer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var query = SelectQuery.from("events")
query = query.order("id", SqlOrder.Desc)
val built = query.build()
val schema = TableSchema.new("events").col(ColumnDef.integer("id"))
val value = DbValue.Integer(value: 11)

expect(quote_ident("events")).to_equal("\"events\"")
expect(built.0).to_contain("ORDER BY")
expect(schema.columns.len()).to_equal(1)
expect(value.db_type()).to_equal(DbType.Integer)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/database/sql/sql_init_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut database SQL package facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
