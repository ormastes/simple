# DataFrame Construction Specification

> Validates construction of `Series<T>` and `DataFrame` from typed sequences, named column maps, and row lists. Covers schema/dtypes/shape/columns accessors and critical error paths (empty frame, mismatched column lengths).

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
| Source | `test/feature/scilib/df_construction_spec.spl` |
| Updated | 2026-08-26 |
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

- returns correct name
   - Expected: s.name() equals `Symbol.from("price")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns correct name")
val s = Series.from_values(
    name: Symbol.from("price"),
    values: [Float64.new(1.5), Float64.new(2.5), Float64.new(3.5)]
)
expect(s.name()).to_equal(Symbol.from("price"))
```

</details>

#### returns correct length

- returns correct length
   - Expected: s.len() equals `Index.new(3)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns correct length")
val s = Series.from_values(
    name: Symbol.from("price"),
    values: [Float64.new(1.5), Float64.new(2.5), Float64.new(3.5)]
)
expect(s.len()).to_equal(Index.new(3))
```

</details>

#### returns DType.F64 for Float64 series

- returns DType.F64 for Float64 series
   - Expected: s.dtype() equals `DType.F64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns DType.F64 for Float64 series")
val s = Series.from_values(
    name: Symbol.from("price"),
    values: [Float64.new(1.5), Float64.new(2.5), Float64.new(3.5)]
)
expect(s.dtype()).to_equal(DType.F64)
```

</details>

#### when constructing Series<Int64>

#### returns DType.I64 for Int64 series

- returns DType.I64 for Int64 series
   - Expected: s.dtype() equals `DType.I64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns DType.I64 for Int64 series")
val s = Series.from_values(
    name: Symbol.from("count"),
    values: [Int64.new(10), Int64.new(20), Int64.new(30)]
)
expect(s.dtype()).to_equal(DType.I64)
```

</details>

#### returns correct length for Int64 series

- returns correct length for Int64 series
   - Expected: s.len() equals `Index.new(2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns correct length for Int64 series")
val s = Series.from_values(
    name: Symbol.from("count"),
    values: [Int64.new(10), Int64.new(20)]
)
expect(s.len()).to_equal(Index.new(2))
```

</details>

#### when constructing an empty Series<Float64>

#### has zero length

- has zero length
   - Expected: s.len() equals `Index.new(0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("has zero length")
val empty_values: [Float64] = []
val s = Series.from_values(
    name: Symbol.from("empty_col"),
    values: empty_values
)
expect(s.len()).to_equal(Index.new(0))
```

</details>

#### preserves DType.F64 on empty series

- preserves DType.F64 on empty series
   - Expected: s.dtype() equals `DType.F64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("preserves DType.F64 on empty series")
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

- schema matches column names in insertion order
   - Expected: schema.len() equals `2`
   - Expected: schema[0] equals `Symbol.from("price")`
   - Expected: schema[1] equals `Symbol.from("qty")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("schema matches column names in insertion order")
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

- num_rows returns row count
   - Expected: df.num_rows() equals `Index.new(3)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("num_rows returns row count")
val price_col = SeriesErased.F64Series(Series.from_values(
    name: Symbol.from("price"),
    values: [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)]
))
val df = DataFrame.from_columns([price_col]).unwrap()
expect(df.num_rows()).to_equal(Index.new(3))
```

</details>

#### num_cols returns column count

- num_cols returns column count
   - Expected: df.num_cols() equals `Index.new(2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("num_cols returns column count")
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

- shape returns (num_rows, num_cols) tuple
   - Expected: s.rows equals `Index.new(3)`
   - Expected: s.cols equals `Index.new(2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("shape returns (num_rows, num_cols) tuple")
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

- dtypes() returns per-column dtype Series
   - Expected: dtypes.len() equals `Index.new(2)`
   - Expected: dtypes.dtype_at(Index.new(0)) equals `DType.F64`
   - Expected: dtypes.dtype_at(Index.new(1)) equals `DType.I64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("dtypes() returns per-column dtype Series")
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

- produces correct column count from row maps
   - Expected: df.num_cols() equals `Index.new(2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("produces correct column count from row maps")
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

- produces correct row count
   - Expected: df.num_rows() equals `Index.new(3)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("produces correct row count")
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

- from_columns with empty list produces zero-column frame
   - Expected: df.num_cols() equals `Index.new(0)`
   - Expected: df.num_rows() equals `Index.new(0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("from_columns with empty list produces zero-column frame")
val columns: [SeriesErased] = []
val df = DataFrame.from_columns(columns).unwrap()
expect(df.num_cols()).to_equal(Index.new(0))
expect(df.num_rows()).to_equal(Index.new(0))
```

</details>

#### dtypes() on empty frame returns zero-length Series

- dtypes() on empty frame returns zero-length Series
   - Expected: df.dtypes().len() equals `Index.new(0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("dtypes() on empty frame returns zero-length Series")
val columns: [SeriesErased] = []
val df = DataFrame.from_columns(columns).unwrap()
expect(df.dtypes().len()).to_equal(Index.new(0))
```

</details>

### DataFrame construction error paths

#### returns ShapeMismatch error for mismatched column lengths

- returns ShapeMismatch error for mismatched column lengths
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns ShapeMismatch error for mismatched column lengths")
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

- ShapeMismatch error variant is DfError.ShapeMismatch
   - Expected: e equals `DfError.ShapeMismatch`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("ShapeMismatch error variant is DfError.ShapeMismatch")
val col_3 = SeriesErased.F64Series(Series.from_values(
    name: Symbol.from("a"),
    values: [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)]
))
val col_2 = SeriesErased.I64Series(Series.from_values(
    name: Symbol.from("b"),
    values: [Int64.new(10), Int64.new(20)]
))
val result = DataFrame.from_columns([col_3, col_2])
match result:
    case Err(e):
        expect(e).to_equal(DfError.ShapeMismatch)
    case Ok(_):
        expect(false).to_equal(true)
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

- **Plan:** `doc/03_plan/agent_tasks/scilib_port_df.md`
- **Design:** `doc/05_design/scilib_port_architecture.md §8`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fb2932cdfd750baf6b080bb5a1f437f7f45784245a79e298c550a1a6d687a2ee`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fb2932cdfd750baf6b080bb5a1f437f7f45784245a79e298c550a1a6d687a2ee`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fb2932cdfd750baf6b080bb5a1f437f7f45784245a79e298c550a1a6d687a2ee`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/feature/scilib/df_construction_spec.spl
mirror: doc/06_spec/feature/scilib/df_construction_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/df_construction_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/df_construction_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/df_construction_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/scilib/df_construction_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns correct name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/df_construction_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns correct length' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/df_construction_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns DType.F64 for Float64 series' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
