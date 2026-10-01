# DataFrame Value Counts / Unique / Nunique Specification

> Validates Series.unique_f64, unique_i64, nunique, and value_counts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame Value Counts / Unique / Nunique Specification

Validates Series.unique_f64, unique_i64, nunique, and value_counts.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | T-DF-32, science-math-lib-set-pandas-core-value-counts |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/scilib_port_df.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/feature/scilib/df_value_counts_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates Series.unique_f64, unique_i64, nunique, and value_counts.

## Scenarios

### Series unique_i64

#### returns deduplicated Int64 values in order of first appearance

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns deduplicated Int64 values in order of first appearance
   - Expected: u.len() equals `Index.new(3)`
   - Expected: u.values.flat_i64(0) equals `Int64.new(3)`
   - Expected: u.values.flat_i64(1) equals `Int64.new(1)`
   - Expected: u.values.flat_i64(2) equals `Int64.new(2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns deduplicated Int64 values in order of first appearance")
val ms = Series.from_i64_masked(
    Symbol.from("group"),
    [Int64.new(3), Int64.new(1), Int64.new(3), Int64.new(2), Int64.new(1)],
    [Bool.new(false), Bool.new(false), Bool.new(false), Bool.new(false), Bool.new(false)]
)
val s = ms.unwrap()
val u = s.unique_i64()
expect(u.len()).to_equal(Index.new(3))
expect(u.values.flat_i64(0)).to_equal(Int64.new(3))
expect(u.values.flat_i64(1)).to_equal(Int64.new(1))
expect(u.values.flat_i64(2)).to_equal(Int64.new(2))
```

</details>

#### returns single-element series for constant column

- returns single-element series for constant column
   - Expected: u.len() equals `Index.new(1)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns single-element series for constant column")
val ms = Series.from_i64_masked(
    Symbol.from("c"),
    [Int64.new(7), Int64.new(7), Int64.new(7)],
    [Bool.new(false), Bool.new(false), Bool.new(false)]
)
val s = ms.unwrap()
val u = s.unique_i64()
expect(u.len()).to_equal(Index.new(1))
```

</details>

### Series nunique

#### returns count of distinct non-missing values for I64 series

- returns count of distinct non-missing values for I64 series
   - Expected: s.nunique() equals `Index.new(3)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns count of distinct non-missing values for I64 series")
val s = Series.from_values(
    name: Symbol.from("x"),
    values: [Float64.new(1.0), Float64.new(2.0), Float64.new(1.0), Float64.new(3.0)]
)
expect(s.nunique()).to_equal(Index.new(3))
```

</details>

#### returns 1 for constant series

- returns 1 for constant series
   - Expected: s.nunique() equals `Index.new(1)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns 1 for constant series")
val s = Series.from_values(
    name: Symbol.from("k"),
    values: [Float64.new(5.0), Float64.new(5.0)]
)
expect(s.nunique()).to_equal(Index.new(1))
```

</details>

#### returns 0 for empty series

- returns 0 for empty series
   - Expected: s.nunique() equals `Index.new(0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns 0 for empty series")
val empty: [Float64] = []
val s = Series.from_values(name: Symbol.from("empty"), values: empty)
expect(s.nunique()).to_equal(Index.new(0))
```

</details>

### value_counts

#### returns a two-column DataFrame with value and count columns

- returns a two-column DataFrame with value and count columns
   - Expected: vc.num_cols() equals `Index.new(2)`
   - Expected: vc.num_rows() equals `Index.new(3)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns a two-column DataFrame with value and count columns")
val s = Series.from_values(
    name: Symbol.from("color"),
    values: [Float64.new(1.0), Float64.new(2.0), Float64.new(1.0), Float64.new(3.0), Float64.new(2.0), Float64.new(2.0)]
)
val vc = value_counts(s)
expect(vc.num_cols()).to_equal(Index.new(2))
expect(vc.num_rows()).to_equal(Index.new(3))
```

</details>

#### count column is named 'count'

- count column is named 'count'
   - Expected: schema[1] equals `Symbol.from("count")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("count column is named 'count'")
val s = Series.from_values(
    name: Symbol.from("grp"),
    values: [Float64.new(1.0), Float64.new(2.0), Float64.new(1.0)]
)
val vc = value_counts(s)
val schema = vc.columns()
expect(schema[1]).to_equal(Symbol.from("count"))
```

</details>

#### count values are correct

- count values are correct
   - Expected: counts.get(Index.new(0)) equals `Int64.new(3)`
   - Expected: counts.get(Index.new(1)) equals `Int64.new(1)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("count values are correct")
val s = Series.from_values(
    name: Symbol.from("g"),
    values: [Float64.new(1.0), Float64.new(2.0), Float64.new(1.0), Float64.new(1.0)]
)
val vc = value_counts(s)
val counts = vc.col(Symbol.from("count")).unwrap()
expect(counts.get(Index.new(0))).to_equal(Int64.new(3))
expect(counts.get(Index.new(1))).to_equal(Int64.new(1))
```

</details>

#### ignores missing values in count

- ignores missing values in count
   - Expected: vc.num_rows() equals `Index.new(1)`
   - Expected: counts.get(Index.new(0)) equals `Int64.new(2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("ignores missing values in count")
val s = Series.from_f64_masked(
    Symbol.from("v"),
    [Float64.new(1.0), Float64.new(0.0), Float64.new(1.0)],
    [Bool.new(false), Bool.new(true), Bool.new(false)]
).unwrap()
val vc = value_counts(s)
expect(vc.num_rows()).to_equal(Index.new(1))
val counts = vc.col(Symbol.from("count")).unwrap()
expect(counts.get(Index.new(0))).to_equal(Int64.new(2))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `d8a0078563eed204f0a19008cfd1ba631598a1dee80842cb6b7345be6984027d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d8a0078563eed204f0a19008cfd1ba631598a1dee80842cb6b7345be6984027d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d8a0078563eed204f0a19008cfd1ba631598a1dee80842cb6b7345be6984027d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/df_value_counts_spec.spl
mirror: doc/06_spec/feature/scilib/df_value_counts_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/df_value_counts_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/df_value_counts_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/df_value_counts_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns deduplicated Int64 values in order of first appearance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/df_value_counts_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns single-element series for constant column' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/df_value_counts_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns count of distinct non-missing values for I64 series' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
