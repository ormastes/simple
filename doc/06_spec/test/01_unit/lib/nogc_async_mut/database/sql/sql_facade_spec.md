# Sql Facade Specification

> <details>

<!-- sdn-diagram:id=sql_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sql_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sql_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sql_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sql Facade Specification

## Scenarios

### nogc_async_mut database SQL facades

#### re-exports pure SQL helper submodules

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(quote_ident("users")).to_equal("\"users\"")
expect(placeholder_list(3)).to_equal("?, ?, ?")
```

</details>

#### re-exports query builder and value types

1. var query = SelectQuery from
2. query = query where eq
3. query = query order
   - Expected: built.1.len() equals `1`
   - Expected: expr.params.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var query = SelectQuery.from("users")
query = query.where_eq("id", DbValue.Integer(value: 7))
query = query.order("name", SqlOrder.Asc)
val built = query.build()
val expr = compile_expr(sql_eq("name", DbValue.Text(value: "Ada")))

expect(built.0).to_contain("WHERE")
expect(built.1.len()).to_equal(1)
expect(expr.params.len()).to_equal(1)
```

</details>

#### re-exports schema builders

1. var schema = TableSchema new
2. schema = schema col
   - Expected: schema.columns.len() equals `1`
   - Expected: value.db_type() equals `DbType.Integer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var schema = TableSchema.new("users")
schema = schema.col(ColumnDef.integer("id").pk())
val value = DbValue.Integer(value: 1)

expect(schema.columns.len()).to_equal(1)
expect(value.db_type()).to_equal(DbType.Integer)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/database/sql/sql_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut database SQL facades

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
