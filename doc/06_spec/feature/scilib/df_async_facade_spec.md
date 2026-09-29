# DataFrame Async/NoGC Facade Specification

> Validates the first namespace-consistency slice from the science math lib set:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame Async/NoGC Facade Specification

Validates the first namespace-consistency slice from the science math lib set:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-async-df-facade |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/feature/scilib/df_async_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates the first namespace-consistency slice from the science math lib set:
`std.nogc_async_mut.df` exposes the same DataFrame seed API as the existing
`std.df` / `std.nogc_sync_mut.df` surface.

## Scenarios

### nogc_async_mut DataFrame facade

#### constructs a DataFrame through the async/nogc namespace

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- constructs a DataFrame through the async/nogc namespace
   - Expected: df.num_rows() equals `Index.new(2)`
   - Expected: df.num_cols() equals `Index.new(2)`
   - Expected: df.columns()[0] equals `Symbol.from("price")`
   - Expected: df.dtypes().dtype_at(Index.new(1)) equals `DType.I64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("constructs a DataFrame through the async/nogc namespace")
val price_col = SeriesErased.F64Series(Series.from_values(
    name: Symbol.from("price"),
    values: [Float64.new(1.0), Float64.new(2.0)]
))
val qty_col = SeriesErased.I64Series(Series.from_values(
    name: Symbol.from("qty"),
    values: [Int64.new(5), Int64.new(8)]
))
val df = DataFrame.from_columns([price_col, qty_col]).unwrap()
expect(df.num_rows()).to_equal(Index.new(2))
expect(df.num_cols()).to_equal(Index.new(2))
expect(df.columns()[0]).to_equal(Symbol.from("price"))
expect(df.dtypes().dtype_at(Index.new(1))).to_equal(DType.I64)
```

</details>

#### uses the same column operation behavior as the sync facade

- uses the same column operation behavior as the sync facade
   - Expected: df2.column_count() equals `Index.new(2)`
   - Expected: b.get(Index.new(1)) equals `Float64.new(20.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses the same column operation behavior as the sync facade")
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(
        name: Symbol.from("a"),
        values: [Float64.new(1.0), Float64.new(2.0)]
    )),
]).unwrap()
val df2 = df.assign(
    Symbol.from("b"),
    SeriesErased.F64Series(Series.from_values(
        name: Symbol.from("b"),
        values: [Float64.new(10.0), Float64.new(20.0)]
    ))
)
val b = df2.col(Symbol.from("b")).unwrap()
expect(df2.column_count()).to_equal(Index.new(2))
expect(b.get(Index.new(1))).to_equal(Float64.new(20.0))
```

</details>

#### exposes reshape helpers through the async/nogc namespace

- exposes reshape helpers through the async/nogc namespace
   - Expected: long.num_rows() equals `Index.new(1)`
   - Expected: long.col(Symbol.from("value")).unwrap().get(Index.new(0)) equals `Float64.new(10.0)`
   - Expected: pivoted.num_cols() equals `Index.new(2)`
   - Expected: pivoted.col(Symbol.from("value_0")).unwrap().get(Index.new(0)) equals `Float64.new(10.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("exposes reshape helpers through the async/nogc namespace")
val wide = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(1)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("jan"), [Float64.new(10.0)])),
]).unwrap()
val long = melt_numeric(
    wide,
    Symbol.from("id"),
    [Symbol.from("jan")],
    Symbol.from("variable"),
    Symbol.from("value")
).unwrap()
expect(long.num_rows()).to_equal(Index.new(1))
expect(long.col(Symbol.from("value")).unwrap().get(Index.new(0))).to_equal(Float64.new(10.0))

val pivoted = pivot_sum(
    long,
    Symbol.from("id"),
    Symbol.from("variable"),
    Symbol.from("value"),
    Symbol.from("value")
).unwrap()
expect(pivoted.num_cols()).to_equal(Index.new(2))
expect(pivoted.col(Symbol.from("value_0")).unwrap().get(Index.new(0))).to_equal(Float64.new(10.0))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/science_math_lib_set.md`
- **Design:** `doc/05_design/science_math_lib_set.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f55701ad1a2515b0fc631568afa9358f2ef3877a4e976a6be095a648700d895c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f55701ad1a2515b0fc631568afa9358f2ef3877a4e976a6be095a648700d895c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f55701ad1a2515b0fc631568afa9358f2ef3877a4e976a6be095a648700d895c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/df_async_facade_spec.spl
mirror: doc/06_spec/feature/scilib/df_async_facade_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/df_async_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/df_async_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/df_async_facade_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs a DataFrame through the async/nogc namespace' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/df_async_facade_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the same column operation behavior as the sync facade' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/df_async_facade_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes reshape helpers through the async/nogc namespace' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
