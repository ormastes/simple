# DataFrame Scalar Broadcast Specification

> Validates Series scalar broadcast methods: add_scalar, sub_scalar, mul_scalar, div_scalar.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame Scalar Broadcast Specification

Validates Series scalar broadcast methods: add_scalar, sub_scalar, mul_scalar, div_scalar.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | T-DF-14, T-DF-15, science-math-lib-set-pandas-core-scalar-broadcast |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/scilib_port_df.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/feature/scilib/df_scalar_broadcast_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates Series scalar broadcast methods: add_scalar, sub_scalar, mul_scalar, div_scalar.
No operator overloading sugar (PERF-SUGAR-003 risk) — explicit method calls only.

## Scenarios

### Series scalar broadcast

#### add_scalar adds rhs to each element

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- add_scalar adds rhs to each element
   - Expected: result.get(Index.new(0)) equals `Float64.new(11.0)`
   - Expected: result.get(Index.new(1)) equals `Float64.new(12.0)`
   - Expected: result.get(Index.new(2)) equals `Float64.new(13.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("add_scalar adds rhs to each element")
val s = Series.from_values(
    name: Symbol.from("price"),
    values: [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)]
)
val result = s.add_scalar(Float64.new(10.0))
expect(result.get(Index.new(0))).to_equal(Float64.new(11.0))
expect(result.get(Index.new(1))).to_equal(Float64.new(12.0))
expect(result.get(Index.new(2))).to_equal(Float64.new(13.0))
```

</details>

#### add_scalar preserves series name

- add_scalar preserves series name
   - Expected: result.name() equals `Symbol.from("x")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("add_scalar preserves series name")
val s = Series.from_values(
    name: Symbol.from("x"),
    values: [Float64.new(5.0)]
)
val result = s.add_scalar(Float64.new(1.0))
expect(result.name()).to_equal(Symbol.from("x"))
```

</details>

#### sub_scalar subtracts rhs from each element

- sub_scalar subtracts rhs from each element
   - Expected: result.get(Index.new(0)) equals `Float64.new(7.0)`
   - Expected: result.get(Index.new(1)) equals `Float64.new(17.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("sub_scalar subtracts rhs from each element")
val s = Series.from_values(
    name: Symbol.from("a"),
    values: [Float64.new(10.0), Float64.new(20.0)]
)
val result = s.sub_scalar(Float64.new(3.0))
expect(result.get(Index.new(0))).to_equal(Float64.new(7.0))
expect(result.get(Index.new(1))).to_equal(Float64.new(17.0))
```

</details>

#### mul_scalar multiplies each element by rhs

- mul_scalar multiplies each element by rhs
   - Expected: result.get(Index.new(0)) equals `Float64.new(6.0)`
   - Expected: result.get(Index.new(1)) equals `Float64.new(12.0)`
   - Expected: result.get(Index.new(2)) equals `Float64.new(18.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("mul_scalar multiplies each element by rhs")
val s = Series.from_values(
    name: Symbol.from("b"),
    values: [Float64.new(2.0), Float64.new(4.0), Float64.new(6.0)]
)
val result = s.mul_scalar(Float64.new(3.0))
expect(result.get(Index.new(0))).to_equal(Float64.new(6.0))
expect(result.get(Index.new(1))).to_equal(Float64.new(12.0))
expect(result.get(Index.new(2))).to_equal(Float64.new(18.0))
```

</details>

#### div_scalar divides each element by rhs

- div_scalar divides each element by rhs
   - Expected: result.get(Index.new(0)) equals `Float64.new(5.0)`
   - Expected: result.get(Index.new(1)) equals `Float64.new(10.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("div_scalar divides each element by rhs")
val s = Series.from_values(
    name: Symbol.from("c"),
    values: [Float64.new(10.0), Float64.new(20.0)]
)
val result = s.div_scalar(Float64.new(2.0)).unwrap()
expect(result.get(Index.new(0))).to_equal(Float64.new(5.0))
expect(result.get(Index.new(1))).to_equal(Float64.new(10.0))
```

</details>

#### div_scalar returns error when rhs is zero

- div_scalar returns error when rhs is zero
   - Expected: s.div_scalar(Float64.new(0.0)).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("div_scalar returns error when rhs is zero")
val s = Series.from_values(
    name: Symbol.from("d"),
    values: [Float64.new(1.0)]
)
expect(s.div_scalar(Float64.new(0.0)).is_err()).to_equal(true)
```

</details>

#### add_scalar returns F64 dtype

- add_scalar returns F64 dtype
   - Expected: result.dtype() equals `DType.F64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("add_scalar returns F64 dtype")
val s = Series.from_values(
    name: Symbol.from("e"),
    values: [Float64.new(1.0), Float64.new(2.0)]
)
val result = s.add_scalar(Float64.new(1.0))
expect(result.dtype()).to_equal(DType.F64)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `e0e1cacdf116aa3cd44159b1338d896144588796aeb3b051af11293bac14a153`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e0e1cacdf116aa3cd44159b1338d896144588796aeb3b051af11293bac14a153`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e0e1cacdf116aa3cd44159b1338d896144588796aeb3b051af11293bac14a153`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/df_scalar_broadcast_spec.spl
mirror: doc/06_spec/feature/scilib/df_scalar_broadcast_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/df_scalar_broadcast_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/df_scalar_broadcast_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/df_scalar_broadcast_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'add_scalar adds rhs to each element' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/df_scalar_broadcast_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'add_scalar preserves series name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/df_scalar_broadcast_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sub_scalar subtracts rhs from each element' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
