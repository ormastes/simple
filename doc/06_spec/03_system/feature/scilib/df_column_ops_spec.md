# DataFrame Column Operations Specification

> DataFrame column-level operations: accessor, assign, drop, rename, dtypes, astype. **DataFrame ops are PLAIN method calls — never inside `math{}`** (architect anti-pattern #2; OQ-A: string-keyed indexing and groupby semantics are structurally incompatible with `MathExpr`).

<!-- sdn-diagram:id=df_column_ops_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=df_column_ops_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

df_column_ops_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=df_column_ops_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame Column Operations Specification

DataFrame column-level operations: accessor, assign, drop, rename, dtypes, astype. **DataFrame ops are PLAIN method calls — never inside `math{}`** (architect anti-pattern #2; OQ-A: string-keyed indexing and groupby semantics are structurally incompatible with `MathExpr`).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | scilib-df-column-ops |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Draft (v1.1 — ships AFTER NDArray + linalg) |
| Plan | doc/03_plan/agent_tasks/scilib_port_df.md |
| Design | doc/05_design/scilib_port_architecture.md |
| Source | `test/03_system/feature/scilib/df_column_ops_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

DataFrame column-level operations: accessor, assign, drop, rename,
dtypes, astype. **DataFrame ops are PLAIN method calls — never inside
`math{}`** (architect anti-pattern #2; OQ-A: string-keyed indexing and
groupby semantics are structurally incompatible with `MathExpr`).

Tasks covered: T-DF-08..14 (column accessor + assign + drop + rename
+ dtypes + astype).

## v1.1 phasing

This file's specs FAIL until v1.1 lands `std.df`. v1 only ships
`std.ndarray` + `std.linalg`. Per `feedback_no_coverups`, the specs are
written with concrete assertions — no `skip()`, no TODO→NOTE — and they
fail naturally until v1.1 impl arrives.

## Method-call vs block-syntax

Pandas-style `df['col']` becomes `df.col("name")` (or the bracket
operator if it lands as a typed wrapper). It is NOT lowered through
`math{}`. The Phase 5/6 impl team must keep the API surface as
plain Simple methods.

## Scenarios

### DataFrame column accessor

#### valid column name

#### returns the requested column as a Series

1. SeriesErased F64Series
2. SeriesErased I64Series
3. ]) unwrap
   - Expected: a.len() equals `Index.new(3)`
   - Expected: a.get(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: a.get(Index.new(2)) equals `Float64.new(3.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("a"), [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])),
    SeriesErased.I64Series(Series.from_values(Symbol.from("b"), [Int64.new(10), Int64.new(20), Int64.new(30)])),
]).unwrap()
val a = df.col(Symbol.from("a")).unwrap()
expect(a.len()).to_equal(Index.new(3))
expect(a.get(Index.new(0))).to_equal(Float64.new(1.0))
expect(a.get(Index.new(2))).to_equal(Float64.new(3.0))
```

</details>

#### missing column name

#### returns an error result

1. SeriesErased F64Series
2. ]) unwrap
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("a"), [Float64.new(1.0), Float64.new(2.0)])),
]).unwrap()
val r = df.col(Symbol.from("not_there"))
expect(r.is_err()).to_equal(true)
```

</details>

### DataFrame assign and drop

#### assign adds a new column to the schema

1. SeriesErased F64Series
2. ]) unwrap
   - Expected: df2.column_count() equals `Index.new(2)`
   - Expected: b.get(Index.new(0)) equals `Float64.new(10.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("a"), [Float64.new(1.0), Float64.new(2.0)])),
]).unwrap()
val df2 = df.assign(Symbol.from("b"), SeriesErased.F64Series(Series.from_values(Symbol.from("b"), [Float64.new(10.0), Float64.new(20.0)])))
expect(df2.column_count()).to_equal(Index.new(2))
val b = df2.col(Symbol.from("b")).unwrap()
expect(b.get(Index.new(0))).to_equal(Float64.new(10.0))
```

</details>

#### assign replaces an existing column

1. SeriesErased F64Series
2. ]) unwrap
   - Expected: df2.column_count() equals `Index.new(1)`
   - Expected: a.get(Index.new(0)) equals `Float64.new(99.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("a"), [Float64.new(1.0), Float64.new(2.0)])),
]).unwrap()
val df2 = df.assign(Symbol.from("a"), SeriesErased.F64Series(Series.from_values(Symbol.from("a"), [Float64.new(99.0), Float64.new(98.0)])))
expect(df2.column_count()).to_equal(Index.new(1))
val a = df2.col(Symbol.from("a")).unwrap()
expect(a.get(Index.new(0))).to_equal(Float64.new(99.0))
```

</details>

#### drop removes the named column

1. SeriesErased F64Series
2. SeriesErased F64Series
3. ]) unwrap
   - Expected: df2.column_count() equals `Index.new(1)`
   - Expected: df2.col(Symbol.from("a")).is_err() is true
   - Expected: b.get(Index.new(0)) equals `Float64.new(2.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("a"), [Float64.new(1.0)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("b"), [Float64.new(2.0)])),
]).unwrap()
val df2 = df.drop(Symbol.from("a")).unwrap()
expect(df2.column_count()).to_equal(Index.new(1))
expect(df2.col(Symbol.from("a")).is_err()).to_equal(true)
val b = df2.col(Symbol.from("b")).unwrap()
expect(b.get(Index.new(0))).to_equal(Float64.new(2.0))
```

</details>

#### drop returns an error when column is missing

1. SeriesErased F64Series
2. ]) unwrap
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("a"), [Float64.new(1.0)])),
]).unwrap()
val r = df.drop(Symbol.from("not_there"))
expect(r.is_err()).to_equal(true)
```

</details>

### DataFrame rename

#### renames an existing column

1. SeriesErased F64Series
2. ]) unwrap
   - Expected: df2.col(Symbol.from("alpha")).unwrap().get(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: df2.col(Symbol.from("a")).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("a"), [Float64.new(1.0), Float64.new(2.0)])),
]).unwrap()
val df2 = df.rename(Symbol.from("a"), Symbol.from("alpha")).unwrap()
expect(df2.col(Symbol.from("alpha")).unwrap().get(Index.new(0))).to_equal(Float64.new(1.0))
expect(df2.col(Symbol.from("a")).is_err()).to_equal(true)
```

</details>

#### errors when new name already exists

1. SeriesErased F64Series
2. SeriesErased F64Series
3. ]) unwrap
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("a"), [Float64.new(1.0)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("b"), [Float64.new(2.0)])),
]).unwrap()
val r = df.rename(Symbol.from("a"), Symbol.from("b"))
expect(r.is_err()).to_equal(true)
```

</details>

### DataFrame dtypes and astype

#### dtypes returns the schema in column order

1. SeriesErased F64Series
2. SeriesErased I64Series
3. ]) unwrap
   - Expected: s.len() equals `Index.new(2)`
   - Expected: s.dtype_at(Index.new(0)) equals `DType.F64`
   - Expected: s.dtype_at(Index.new(1)) equals `DType.I64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("a"), [Float64.new(1.0)])),
    SeriesErased.I64Series(Series.from_values(Symbol.from("b"), [Int64.new(10)])),
]).unwrap()
val s = df.dtypes()
expect(s.len()).to_equal(Index.new(2))
expect(s.dtype_at(Index.new(0))).to_equal(DType.F64)
expect(s.dtype_at(Index.new(1))).to_equal(DType.I64)
```

</details>

#### astype converts Int64 column to Float64

1. SeriesErased I64Series
2. ]) unwrap
   - Expected: a.dtype equals `DType.F64`
   - Expected: a.get(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: a.get(Index.new(2)) equals `Float64.new(3.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("a"), [Int64.new(1), Int64.new(2), Int64.new(3)])),
]).unwrap()
val df2 = df.astype(Symbol.from("a"), DType.F64).unwrap()
val a = df2.col(Symbol.from("a")).unwrap()
expect(a.dtype).to_equal(DType.F64)
expect(a.get(Index.new(0))).to_equal(Float64.new(1.0))
expect(a.get(Index.new(2))).to_equal(Float64.new(3.0))
```

</details>

### DataFrame ops do NOT participate in math{}

#### df.col(...).add(other) goes through Series methods, not math{}

1. SeriesErased F64Series
2. SeriesErased F64Series
3. ]) unwrap
   - Expected: r.len() equals `Index.new(2)`
   - Expected: r.get(Index.new(0)) equals `Float64.new(11.0)`
   - Expected: r.get(Index.new(1)) equals `Float64.new(22.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("a"), [Float64.new(1.0), Float64.new(2.0)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("b"), [Float64.new(10.0), Float64.new(20.0)])),
]).unwrap()
val a = df.col(Symbol.from("a")).unwrap()
val b = df.col(Symbol.from("b")).unwrap()
val r = a.add(b)
expect(r.len()).to_equal(Index.new(2))
expect(r.get(Index.new(0))).to_equal(Float64.new(11.0))
expect(r.get(Index.new(1))).to_equal(Float64.new(22.0))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/scilib_port_df.md](doc/03_plan/agent_tasks/scilib_port_df.md)
- **Design:** [doc/05_design/scilib_port_architecture.md](doc/05_design/scilib_port_architecture.md)


</details>
