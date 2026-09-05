# DataFrame Column Operations Specification

> DataFrame column-level operations: accessor, assign, drop, rename, dtypes, astype. **DataFrame ops are PLAIN method calls — never inside `math{}`** (architect anti-pattern #2; OQ-A: string-keyed indexing and groupby semantics are structurally incompatible with `MathExpr`).

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
| Source | `test/feature/scilib/df_column_ops_spec.spl` |
| Updated | 2026-08-26 |
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

- returns the requested column as a Series
   - Expected: a.len() equals `Index.new(3)`
   - Expected: a.get(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: a.get(Index.new(2)) equals `Float64.new(3.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns the requested column as a Series")
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

- returns an error result
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns an error result")
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("a"), [Float64.new(1.0), Float64.new(2.0)])),
]).unwrap()
val r = df.col(Symbol.from("not_there"))
expect(r.is_err()).to_equal(true)
```

</details>

### DataFrame assign and drop

#### assign adds a new column to the schema

- assign adds a new column to the schema
   - Expected: df2.column_count() equals `Index.new(2)`
   - Expected: b.get(Index.new(0)) equals `Float64.new(10.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("assign adds a new column to the schema")
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

- assign replaces an existing column
   - Expected: df2.column_count() equals `Index.new(1)`
   - Expected: a.get(Index.new(0)) equals `Float64.new(99.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("assign replaces an existing column")
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

- drop removes the named column
   - Expected: df2.column_count() equals `Index.new(1)`
   - Expected: df2.col(Symbol.from("a")).is_err() is true
   - Expected: b.get(Index.new(0)) equals `Float64.new(2.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("drop removes the named column")
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

- drop returns an error when column is missing
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("drop returns an error when column is missing")
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("a"), [Float64.new(1.0)])),
]).unwrap()
val r = df.drop(Symbol.from("not_there"))
expect(r.is_err()).to_equal(true)
```

</details>

### DataFrame rename

#### renames an existing column

- renames an existing column
   - Expected: df2.col(Symbol.from("alpha")).unwrap().get(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: df2.col(Symbol.from("a")).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("renames an existing column")
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("a"), [Float64.new(1.0), Float64.new(2.0)])),
]).unwrap()
val df2 = df.rename(Symbol.from("a"), Symbol.from("alpha")).unwrap()
expect(df2.col(Symbol.from("alpha")).unwrap().get(Index.new(0))).to_equal(Float64.new(1.0))
expect(df2.col(Symbol.from("a")).is_err()).to_equal(true)
```

</details>

#### errors when new name already exists

- errors when new name already exists
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("errors when new name already exists")
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

- dtypes returns the schema in column order
   - Expected: s.len() equals `Index.new(2)`
   - Expected: s.dtype_at(Index.new(0)) equals `DType.F64`
   - Expected: s.dtype_at(Index.new(1)) equals `DType.I64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("dtypes returns the schema in column order")
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

- astype converts Int64 column to Float64
   - Expected: a.dtype equals `DType.F64`
   - Expected: a.get(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: a.get(Index.new(2)) equals `Float64.new(3.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("astype converts Int64 column to Float64")
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

- df.col(...).add(other) goes through Series methods, not math{}
   - Expected: r.len() equals `Index.new(2)`
   - Expected: r.get(Index.new(0)) equals `Float64.new(11.0)`
   - Expected: r.get(Index.new(1)) equals `Float64.new(22.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("df.col(...).add(other) goes through Series methods, not math{}")
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

- **Plan:** `doc/03_plan/agent_tasks/scilib_port_df.md`
- **Design:** `doc/05_design/scilib_port_architecture.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0b4cd6c04007c78c82e61cc18400e947072fa6c2f31d98df241273b847506554`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0b4cd6c04007c78c82e61cc18400e947072fa6c2f31d98df241273b847506554`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0b4cd6c04007c78c82e61cc18400e947072fa6c2f31d98df241273b847506554`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/df_column_ops_spec.spl
mirror: doc/06_spec/feature/scilib/df_column_ops_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/df_column_ops_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/df_column_ops_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/df_column_ops_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the requested column as a Series' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/df_column_ops_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns an error result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/df_column_ops_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'assign adds a new column to the schema' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
