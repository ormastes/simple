# DataFrame Construction Specification

> Validates construction of `Series<T>` and `DataFrame` from typed sequences, named column maps, and row lists. Covers schema/dtypes/shape/columns accessors and critical error paths (empty frame, mismatched column lengths).

<!-- sdn-diagram:id=df_construction_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=df_construction_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

df_construction_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=df_construction_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame Construction Specification

Validates construction of `Series<T>` and `DataFrame` from typed sequences, named column maps, and row lists. Covers schema/dtypes/shape/columns accessors and critical error paths (empty frame, mismatched column lengths).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #T-DF-04, #T-DF-05, #T-DF-06, #T-DF-07 |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Draft |
| Plan | doc/03_plan/agent_tasks/scilib_port_df.md |
| Design | doc/05_design/scilib_port_architecture.md §8 |
| Source | `test/03_system/feature/scilib/df_construction_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates construction of `Series<T>` and `DataFrame` from typed sequences,
named column maps, and row lists. Covers schema/dtypes/shape/columns accessors
and critical error paths (empty frame, mismatched column lengths).

## Phase Note

These specs are v1.1 — they FAIL until Phase 5 ships NDArray (v1) and Phase 5
ships the df library (v1.1). Failure is expected and correct until then.
All specs run via `bin/simple test` in interpreter mode; no `--mode=native`.
`SIMPLE_BLAS_BACKEND=mock` must be set (NDArray backing).

## Anti-Pattern Reminder

DataFrame ops are NEVER inside `math{}` blocks. String-keyed column indexing is
fundamentally incompatible with `MathExpr` (architect anti-pattern #2, AC-3).
All construction and accessor calls in this spec are plain Simple method calls.

## Key Concepts

| Concept        | Description                                              |
|----------------|----------------------------------------------------------|
| Series<T>      | Typed 1-D column backed by NDArray<T>                   |
| DataFrame      | Collection of SeriesErased columns sharing a row index   |
| SeriesErased   | Enum wrapping typed Series variants for heterogeneous df |
| Symbol         | Interned column name (fallback: Symbol = text in v1.1)  |
| DfError        | Error enum: ShapeMismatch, ColumnNotFound, etc.          |

## Scenarios

### Series construction

#### when constructing Series<Float64>

#### returns correct name

1. name: Symbol from
2. values: [Float64 new
   - Expected: s.name() equals `Symbol.from("price")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Series.from_values(
    name: Symbol.from("price"),
    values: [Float64.new(1.5), Float64.new(2.5), Float64.new(3.5)]
)
expect(s.name()).to_equal(Symbol.from("price"))
```

</details>

#### returns correct length

1. name: Symbol from
2. values: [Float64 new
   - Expected: s.len() equals `Index.new(3)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Series.from_values(
    name: Symbol.from("price"),
    values: [Float64.new(1.5), Float64.new(2.5), Float64.new(3.5)]
)
expect(s.len()).to_equal(Index.new(3))
```

</details>

#### returns DType.F64 for Float64 series

1. name: Symbol from
2. values: [Float64 new
   - Expected: s.dtype() equals `DType.F64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Series.from_values(
    name: Symbol.from("price"),
    values: [Float64.new(1.5), Float64.new(2.5), Float64.new(3.5)]
)
expect(s.dtype()).to_equal(DType.F64)
```

</details>

#### when constructing Series<Int64>

#### returns DType.I64 for Int64 series

1. name: Symbol from
2. values: [Int64 new
   - Expected: s.dtype() equals `DType.I64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Series.from_values(
    name: Symbol.from("count"),
    values: [Int64.new(10), Int64.new(20), Int64.new(30)]
)
expect(s.dtype()).to_equal(DType.I64)
```

</details>

#### returns correct length for Int64 series

1. name: Symbol from
2. values: [Int64 new
   - Expected: s.len() equals `Index.new(2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Series.from_values(
    name: Symbol.from("count"),
    values: [Int64.new(10), Int64.new(20)]
)
expect(s.len()).to_equal(Index.new(2))
```

</details>

#### when constructing an empty Series<Float64>

#### has zero length

1. name: Symbol from
   - Expected: s.len() equals `Index.new(0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_values: [Float64] = []
val s = Series.from_values(
    name: Symbol.from("empty_col"),
    values: empty_values
)
expect(s.len()).to_equal(Index.new(0))
```

</details>

#### preserves DType.F64 on empty series

1. name: Symbol from
   - Expected: s.dtype() equals `DType.F64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_values: [Float64] = []
val s = Series.from_values(
    name: Symbol.from("empty_col"),
    values: empty_values
)
expect(s.dtype()).to_equal(DType.F64)
```

</details>

### DataFrame construction from columns

#### when given two typed columns of equal length

#### schema matches column names in insertion order

1. name: Symbol from
2. values: [Float64 new
3. name: Symbol from
4. values: [Int64 new
   - Expected: schema.len() equals `2`
   - Expected: schema[0] equals `Symbol.from("price")`
   - Expected: schema[1] equals `Symbol.from("qty")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val price_col = SeriesErased.F64Series(Series.from_values(
    name: Symbol.from("price"),
    values: [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)]
))
val qty_col = SeriesErased.I64Series(Series.from_values(
    name: Symbol.from("qty"),
    values: [Int64.new(5), Int64.new(10), Int64.new(15)]
))
val df = DataFrame.from_columns([price_col, qty_col]).unwrap()
val schema = df.columns()
expect(schema.len()).to_equal(2)
expect(schema[0]).to_equal(Symbol.from("price"))
expect(schema[1]).to_equal(Symbol.from("qty"))
```

</details>

#### num_rows returns row count

1. name: Symbol from
2. values: [Float64 new
   - Expected: df.num_rows() equals `Index.new(3)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val price_col = SeriesErased.F64Series(Series.from_values(
    name: Symbol.from("price"),
    values: [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)]
))
val df = DataFrame.from_columns([price_col]).unwrap()
expect(df.num_rows()).to_equal(Index.new(3))
```

</details>

#### num_cols returns column count

1. name: Symbol from
2. values: [Float64 new
3. name: Symbol from
4. values: [Int64 new
   - Expected: df.num_cols() equals `Index.new(2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val price_col = SeriesErased.F64Series(Series.from_values(
    name: Symbol.from("price"),
    values: [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)]
))
val qty_col = SeriesErased.I64Series(Series.from_values(
    name: Symbol.from("qty"),
    values: [Int64.new(5), Int64.new(10), Int64.new(15)]
))
val df = DataFrame.from_columns([price_col, qty_col]).unwrap()
expect(df.num_cols()).to_equal(Index.new(2))
```

</details>

#### shape returns (num_rows, num_cols) tuple

1. name: Symbol from
2. values: [Float64 new
3. name: Symbol from
4. values: [Int64 new
   - Expected: s.rows equals `Index.new(3)`
   - Expected: s.cols equals `Index.new(2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val price_col = SeriesErased.F64Series(Series.from_values(
    name: Symbol.from("price"),
    values: [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)]
))
val qty_col = SeriesErased.I64Series(Series.from_values(
    name: Symbol.from("qty"),
    values: [Int64.new(5), Int64.new(10), Int64.new(15)]
))
val df = DataFrame.from_columns([price_col, qty_col]).unwrap()
val s = df.shape()
expect(s.rows).to_equal(Index.new(3))
expect(s.cols).to_equal(Index.new(2))
```

</details>

#### dtypes() returns per-column dtype Series

1. name: Symbol from
2. values: [Float64 new
3. name: Symbol from
4. values: [Int64 new
   - Expected: dtypes.len() equals `Index.new(2)`
   - Expected: dtypes.dtype_at(Index.new(0)) equals `DType.F64`
   - Expected: dtypes.dtype_at(Index.new(1)) equals `DType.I64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val price_col = SeriesErased.F64Series(Series.from_values(
    name: Symbol.from("price"),
    values: [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)]
))
val qty_col = SeriesErased.I64Series(Series.from_values(
    name: Symbol.from("qty"),
    values: [Int64.new(5), Int64.new(10), Int64.new(15)]
))
val df = DataFrame.from_columns([price_col, qty_col]).unwrap()
val dtypes = df.dtypes()
expect(dtypes.len()).to_equal(Index.new(2))
expect(dtypes.dtype_at(Index.new(0))).to_equal(DType.F64)
expect(dtypes.dtype_at(Index.new(1))).to_equal(DType.I64)
```

</details>

### DataFrame construction from rows

#### when given uniform rows

#### produces correct column count from row maps

1. [RowEntry new
2. RowEntry new
3. [RowEntry new
4. RowEntry new
   - Expected: df.num_cols() equals `Index.new(2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = [
    [RowEntry.new(Symbol.from("x"), DfValue.F64(Float64.new(1.0))),
     RowEntry.new(Symbol.from("y"), DfValue.I64(Int64.new(10)))],
    [RowEntry.new(Symbol.from("x"), DfValue.F64(Float64.new(2.0))),
     RowEntry.new(Symbol.from("y"), DfValue.I64(Int64.new(20)))]
]
val df = DataFrame.from_rows(rows).unwrap()
expect(df.num_cols()).to_equal(Index.new(2))
```

</details>

#### produces correct row count

1. [RowEntry new
2. [RowEntry new
3. [RowEntry new
   - Expected: df.num_rows() equals `Index.new(3)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = [
    [RowEntry.new(Symbol.from("x"), DfValue.F64(Float64.new(1.0)))],
    [RowEntry.new(Symbol.from("x"), DfValue.F64(Float64.new(2.0)))],
    [RowEntry.new(Symbol.from("x"), DfValue.F64(Float64.new(3.0)))]
]
val df = DataFrame.from_rows(rows).unwrap()
expect(df.num_rows()).to_equal(Index.new(3))
```

</details>

### Empty DataFrame edge cases

#### from_columns with empty list produces zero-column frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val columns: [SeriesErased] = []
val df = DataFrame.from_columns(columns).unwrap()
expect(df.num_cols()).to_equal(Index.new(0))
expect(df.num_rows()).to_equal(Index.new(0))
```

</details>

#### dtypes() on empty frame returns zero-length Series

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val columns: [SeriesErased] = []
val df = DataFrame.from_columns(columns).unwrap()
expect(df.dtypes().len()).to_equal(Index.new(0))
```

</details>

### DataFrame construction error paths

#### returns ShapeMismatch error for mismatched column lengths

1. name: Symbol from
2. values: [Float64 new
3. name: Symbol from
4. values: [Int64 new
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col_3 = SeriesErased.F64Series(Series.from_values(
    name: Symbol.from("a"),
    values: [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)]
))
val col_2 = SeriesErased.I64Series(Series.from_values(
    name: Symbol.from("b"),
    values: [Int64.new(10), Int64.new(20)]
))
val result = DataFrame.from_columns([col_3, col_2])
expect(result.is_err()).to_equal(true)
```

</details>

#### ShapeMismatch error variant is DfError.ShapeMismatch

1. name: Symbol from
2. values: [Float64 new
3. name: Symbol from
4. values: [Int64 new
   - Expected: observed_error equals `DfError.ShapeMismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val col_3 = SeriesErased.F64Series(Series.from_values(
    name: Symbol.from("a"),
    values: [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)]
))
val col_2 = SeriesErased.I64Series(Series.from_values(
    name: Symbol.from("b"),
    values: [Int64.new(10), Int64.new(20)]
))
val result = DataFrame.from_columns([col_3, col_2])
var observed_error = DfError.ShapeMismatch
match result:
    case Err(e):
        observed_error = e
    case Ok(_):
        observed_error = DfError.ColumnNotFound
expect(observed_error).to_equal(DfError.ShapeMismatch)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/scilib_port_df.md](doc/03_plan/agent_tasks/scilib_port_df.md)
- **Design:** [doc/05_design/scilib_port_architecture.md §8](doc/05_design/scilib_port_architecture.md §8)


</details>
