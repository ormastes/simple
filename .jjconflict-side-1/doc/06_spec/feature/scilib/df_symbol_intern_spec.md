# DataFrame Symbol Interning Specification

> Validates PERF-SUGAR-006: DataFrame column-name Symbols keep their text labels

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame Symbol Interning Specification

Validates PERF-SUGAR-006: DataFrame column-name Symbols keep their text labels

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/feature/scilib/df_symbol_intern_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates PERF-SUGAR-006: DataFrame column-name Symbols keep their text labels
while using stable intern ids for repeated name lookups and duplicate checks.

## Scenarios

### DataFrame Symbol intern ids

#### reuses ids for equal text and keeps distinct ids for different text

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reuses ids for equal text and keeps distinct ids for different text
   - Expected: a1.intern_id() equals `a2.intern_id()`
   - Expected: a1.intern_id() != b.intern_id() is true
   - Expected: a1.label() equals `alpha`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reuses ids for equal text and keeps distinct ids for different text")
val a1 = Symbol.from("alpha")
val a2 = Symbol.from("alpha")
val b = Symbol.from("beta")
expect(a1.intern_id()).to_equal(a2.intern_id())
expect(a1.intern_id() != b.intern_id()).to_equal(true)
expect(a1.label()).to_equal("alpha")
```

</details>

#### selects with freshly constructed same-text symbols

- selects with freshly constructed same-text symbols
   - Expected: selected.columns()[0].intern_id() equals `Symbol.from("extra").intern_id()`
   - Expected: selected.columns()[1].intern_id() equals `Symbol.from("value").intern_id()`
   - Expected: selected.col(Symbol.from("value")).unwrap().get(Index.new(1)) equals `Float64.new(20.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("selects with freshly constructed same-text symbols")
val selected = _base_df().select([Symbol.from("extra"), Symbol.from("value")]).unwrap()
expect(selected.columns()[0].intern_id()).to_equal(Symbol.from("extra").intern_id())
expect(selected.columns()[1].intern_id()).to_equal(Symbol.from("value").intern_id())
expect(selected.col(Symbol.from("value")).unwrap().get(Index.new(1))).to_equal(Float64.new(20.0))
```

</details>

#### detects duplicate rename targets by intern id

- detects duplicate rename targets by intern id
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("detects duplicate rename targets by intern id")
val result = _base_df().rename(Symbol.from("extra"), Symbol.from("value"))
expect(result.is_err()).to_equal(true)
```

</details>

#### groups with freshly constructed same-text symbols

- groups with freshly constructed same-text symbols
   - Expected: grouped.col(Symbol.from("id")).unwrap().values.flat_i64(0) equals `Int64.new(1)`
   - Expected: grouped.col(Symbol.from("value")).unwrap().values.flat_f64(0) equals `Float64.new(15.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("groups with freshly constructed same-text symbols")
val grouped = _base_df().groupby_sum(Symbol.from("id"), Symbol.from("value")).unwrap()
expect(grouped.col(Symbol.from("id")).unwrap().values.flat_i64(0)).to_equal(Int64.new(1))
expect(grouped.col(Symbol.from("value")).unwrap().values.flat_f64(0)).to_equal(Float64.new(15.0))
```

</details>

#### concat rows accepts independently interned same schemas

- concat rows accepts independently interned same schemas
   - Expected: out.num_rows() equals `Index.new(6)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("concat rows accepts independently interned same schemas")
val left = _base_df().select([Symbol.from("id"), Symbol.from("value")]).unwrap()
val right = _base_df().select([Symbol.from("id"), Symbol.from("value")]).unwrap()
val out = concat([left, right], ConcatAxis.Rows).unwrap()
expect(out.num_rows()).to_equal(Index.new(6))
```

</details>

#### concat columns rejects duplicate fresh same-text names

- concat columns rejects duplicate fresh same-text names
   - Expected: concat([left, right], ConcatAxis.Cols).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("concat columns rejects duplicate fresh same-text names")
val left = _base_df().select([Symbol.from("id")]).unwrap()
val right = _base_df().select([Symbol.from("id")]).unwrap()
expect(concat([left, right], ConcatAxis.Cols).is_err()).to_equal(true)
```

</details>

#### merge skips the right join key by intern id

- merge skips the right join key by intern id
   - Expected: out.num_cols() equals `Index.new(3)`
   - Expected: out.col(Symbol.from("right_value")).unwrap().get(Index.new(0)) equals `Float64.new(3.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("merge skips the right join key by intern id")
val left = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(1), Int64.new(2)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("left_value"), [Float64.new(10.0), Float64.new(20.0)])),
]).unwrap()
val right = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(2)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("right_value"), [Float64.new(3.0)])),
]).unwrap()
val out = merge(left, right, Symbol.from("id"), JoinHow.Inner).unwrap()
expect(out.num_cols()).to_equal(Index.new(3))
expect(out.col(Symbol.from("right_value")).unwrap().get(Index.new(0))).to_equal(Float64.new(3.0))
```

</details>

#### melt and pivot reject duplicate symbol arguments by intern id

- melt and pivot reject duplicate symbol arguments by intern id
   - Expected: df.melt_numeric(Symbol.from("id"), [Symbol.from("value")], Symbol.from("id"), Symbol.from("melt_value")).is_err() is true
   - Expected: df.pivot_sum(Symbol.from("id"), Symbol.from("id"), Symbol.from("value"), Symbol.from("value")).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("melt and pivot reject duplicate symbol arguments by intern id")
val df = _base_df()
expect(df.melt_numeric(Symbol.from("id"), [Symbol.from("value")], Symbol.from("id"), Symbol.from("melt_value")).is_err()).to_equal(true)
expect(df.pivot_sum(Symbol.from("id"), Symbol.from("id"), Symbol.from("value"), Symbol.from("value")).is_err()).to_equal(true)
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7e1778162a6b3a5dd5ba9d7edea8fc172fdac7fae03d24e69a0f51e6bd27fae0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7e1778162a6b3a5dd5ba9d7edea8fc172fdac7fae03d24e69a0f51e6bd27fae0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7e1778162a6b3a5dd5ba9d7edea8fc172fdac7fae03d24e69a0f51e6bd27fae0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/df_symbol_intern_spec.spl
mirror: doc/06_spec/feature/scilib/df_symbol_intern_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/df_symbol_intern_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/df_symbol_intern_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/df_symbol_intern_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reuses ids for equal text and keeps distinct ids for different text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/df_symbol_intern_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects with freshly constructed same-text symbols' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/df_symbol_intern_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects duplicate rename targets by intern id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
