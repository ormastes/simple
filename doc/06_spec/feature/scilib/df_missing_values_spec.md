# DataFrame Missing Values Specification

> Validates is_na, fill_na, drop_na on Series and DataFrame.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame Missing Values Specification

Validates is_na, fill_na, drop_na on Series and DataFrame.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | T-DF-16, T-DF-17, science-math-lib-set-pandas-core-missing |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/scilib_port_df.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/feature/scilib/df_missing_values_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates is_na, fill_na, drop_na on Series and DataFrame.

## Scenarios

### Series is_na

#### returns Bool series marking missing positions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns Bool series marking missing positions
   - Expected: na2.len() equals `Index.new(3)`
   - Expected: na3.values.flat_bool(0) equals `Bool.new(false)`
   - Expected: na4.values.flat_bool(1) equals `Bool.new(true)`
   - Expected: na5.values.flat_bool(2) equals `Bool.new(false)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns Bool series marking missing positions")
val masked = Series.from_f64_masked(
    Symbol.from("x"),
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Bool.new(false), Bool.new(true), Bool.new(false)]
)
val s = masked.unwrap()
var na2 = s.is_na()
expect(na2.len()).to_equal(Index.new(3))
# verify via flat_bool: position 1 is missing, others are not
var na3 = s.is_na()
expect(na3.values.flat_bool(0)).to_equal(Bool.new(false))
var na4 = s.is_na()
expect(na4.values.flat_bool(1)).to_equal(Bool.new(true))
var na5 = s.is_na()
expect(na5.values.flat_bool(2)).to_equal(Bool.new(false))
```

</details>

#### returns all-false Bool series when no values are missing

- returns all-false Bool series when no values are missing
   - Expected: na.values.flat_bool(0) equals `Bool.new(false)`
   - Expected: na2.values.flat_bool(1) equals `Bool.new(false)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns all-false Bool series when no values are missing")
val s = Series.from_values(
    name: Symbol.from("y"),
    values: [Float64.new(1.0), Float64.new(2.0)]
)
var na = s.is_na()
expect(na.values.flat_bool(0)).to_equal(Bool.new(false))
var na2 = s.is_na()
expect(na2.values.flat_bool(1)).to_equal(Bool.new(false))
```

</details>

### Series fill_na

#### replaces missing Float64 values with fill value

- replaces missing Float64 values with fill value
   - Expected: filled.get(Index.new(1)) equals `Float64.new(99.0)`
   - Expected: filled.is_missing(Index.new(1)).unwrap() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("replaces missing Float64 values with fill value")
val s = Series.from_f64_masked(
    Symbol.from("x"),
    [Float64.new(1.0), Float64.new(0.0), Float64.new(3.0)],
    [Bool.new(false), Bool.new(true), Bool.new(false)]
).unwrap()
val filled = s.fill_na(Float64.new(99.0))
expect(filled.get(Index.new(1))).to_equal(Float64.new(99.0))
expect(filled.is_missing(Index.new(1)).unwrap()).to_equal(false)
```

</details>

#### leaves non-missing values unchanged

- leaves non-missing values unchanged
   - Expected: filled.get(Index.new(0)) equals `Float64.new(5.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("leaves non-missing values unchanged")
val s = Series.from_f64_masked(
    Symbol.from("a"),
    [Float64.new(5.0), Float64.new(0.0)],
    [Bool.new(false), Bool.new(true)]
).unwrap()
val filled = s.fill_na(Float64.new(0.0))
expect(filled.get(Index.new(0))).to_equal(Float64.new(5.0))
```

</details>

### DataFrame is_na

#### returns boolean DataFrame with same schema

- returns boolean DataFrame with same schema
   - Expected: na_df.num_cols() equals `Index.new(2)`
   - Expected: col_a.values.flat_bool(1) equals `Bool.new(true)`
   - Expected: col_b.values.flat_bool(0) equals `Bool.new(false)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns boolean DataFrame with same schema")
val sa = Series.from_f64_masked(
    Symbol.from("a"),
    [Float64.new(1.0), Float64.new(0.0)],
    [Bool.new(false), Bool.new(true)]
)
val sb = Series.from_i64_masked(
    Symbol.from("b"),
    [Int64.new(10), Int64.new(20)],
    [Bool.new(false), Bool.new(false)]
)
val df = DataFrame.from_columns([
    SeriesErased.F64Series(sa.unwrap()),
    SeriesErased.I64Series(sb.unwrap()),
]).unwrap()
val na_df = df.is_na()
expect(na_df.num_cols()).to_equal(Index.new(2))
val col_a_r = na_df.col(Symbol.from("a"))
val col_a = col_a_r.unwrap()
expect(col_a.values.flat_bool(1)).to_equal(Bool.new(true))
val col_b_r = na_df.col(Symbol.from("b"))
val col_b = col_b_r.unwrap()
expect(col_b.values.flat_bool(0)).to_equal(Bool.new(false))
```

</details>

### DataFrame drop_na

#### Any: drops rows where at least one column is missing

- Any: drops rows where at least one column is missing
   - Expected: out.num_rows() equals `Index.new(2)`
   - Expected: out.col(Symbol.from("x")).unwrap().get(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: out.col(Symbol.from("x")).unwrap().get(Index.new(1)) equals `Float64.new(3.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Any: drops rows where at least one column is missing")
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_f64_masked(
        Symbol.from("x"),
        [Float64.new(1.0), Float64.new(0.0), Float64.new(3.0)],
        [Bool.new(false), Bool.new(true), Bool.new(false)]
    ).unwrap()),
    SeriesErased.I64Series(Series.from_i64_masked(
        Symbol.from("y"),
        [Int64.new(10), Int64.new(20), Int64.new(30)],
        [Bool.new(false), Bool.new(false), Bool.new(false)]
    ).unwrap()),
]).unwrap()
val out = df.drop_na(NaHow.Any)
expect(out.num_rows()).to_equal(Index.new(2))
expect(out.col(Symbol.from("x")).unwrap().get(Index.new(0))).to_equal(Float64.new(1.0))
expect(out.col(Symbol.from("x")).unwrap().get(Index.new(1))).to_equal(Float64.new(3.0))
```

</details>

#### All: only drops rows where all columns are missing

- All: only drops rows where all columns are missing
   - Expected: out.num_rows() equals `Index.new(2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("All: only drops rows where all columns are missing")
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_f64_masked(
        Symbol.from("x"),
        [Float64.new(1.0), Float64.new(0.0), Float64.new(3.0)],
        [Bool.new(false), Bool.new(true), Bool.new(false)]
    ).unwrap()),
    SeriesErased.I64Series(Series.from_i64_masked(
        Symbol.from("y"),
        [Int64.new(10), Int64.new(0), Int64.new(30)],
        [Bool.new(false), Bool.new(true), Bool.new(false)]
    ).unwrap()),
]).unwrap()
val out = df.drop_na(NaHow.All)
expect(out.num_rows()).to_equal(Index.new(2))
```

</details>

#### Any on frame with no missing values leaves all rows

- Any on frame with no missing values leaves all rows
   - Expected: out.num_rows() equals `Index.new(2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Any on frame with no missing values leaves all rows")
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(
        name: Symbol.from("a"),
        values: [Float64.new(1.0), Float64.new(2.0)]
    )),
]).unwrap()
val out = df.drop_na(NaHow.Any)
expect(out.num_rows()).to_equal(Index.new(2))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/scilib_port_df.md`
- **Design:** `doc/05_design/science_math_lib_set.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ab164a02bed09349e08cc0acd5bfc6262bf7aebae0722e33605e6ad52c1eef8c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ab164a02bed09349e08cc0acd5bfc6262bf7aebae0722e33605e6ad52c1eef8c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ab164a02bed09349e08cc0acd5bfc6262bf7aebae0722e33605e6ad52c1eef8c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/df_missing_values_spec.spl
mirror: doc/06_spec/feature/scilib/df_missing_values_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/df_missing_values_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/df_missing_values_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/df_missing_values_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns Bool series marking missing positions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/df_missing_values_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns all-false Bool series when no values are missing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/df_missing_values_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'replaces missing Float64 values with fill value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
