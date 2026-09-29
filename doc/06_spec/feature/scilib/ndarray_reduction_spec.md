# NDArray Reduction Specification

> Validates the first NumPy-core reduction slice for F64 NDArrays. Axis-aware

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NDArray Reduction Specification

Validates the first NumPy-core reduction slice for F64 NDArrays. Axis-aware

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-numpy-core-reductions |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/feature/scilib/ndarray_reduction_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates the first NumPy-core reduction slice for F64 NDArrays. Axis-aware
reductions are planned separately; this spec covers whole-array reductions and
their Result-based error paths.

## Scenarios

### NDArray whole-array reductions

#### computes sum, mean, min, max, and argmax over a 1-D Float64 array

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- computes sum, mean, min, max, and argmax over a 1-D Float64 array
   - Expected: a.sum() equals `Float64.new(10.0)`
   - Expected: a.mean() equals `Float64.new(2.5)`
   - Expected: a.min() equals `Float64.new(-1.0)`
   - Expected: a.max() equals `Float64.new(5.0)`
   - Expected: a.argmax() equals `Index.new(2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes sum, mean, min, max, and argmax over a 1-D Float64 array")
val a = array([Float64.new(2.0), Float64.new(-1.0), Float64.new(5.0), Float64.new(4.0)])
expect(a.sum()).to_equal(Float64.new(10.0))
expect(a.mean()).to_equal(Float64.new(2.5))
expect(a.min()).to_equal(Float64.new(-1.0))
expect(a.max()).to_equal(Float64.new(5.0))
expect(a.argmax()).to_equal(Index.new(2))
```

</details>

#### computes contiguous Float64 sum and mean through SIMD chunks with a scalar tail

- computes contiguous Float64 sum and mean through SIMD chunks with a scalar tail
   - Expected: a.sum() equals `Float64.new(21.0)`
   - Expected: a.mean() equals `Float64.new(3.5)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes contiguous Float64 sum and mean through SIMD chunks with a scalar tail")
val a = array([
    Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0),
    Float64.new(5.0), Float64.new(6.0)])
expect(a.sum()).to_equal(Float64.new(21.0))
expect(a.mean()).to_equal(Float64.new(3.5))
```

</details>

#### computes contiguous Float32 sum and mean through SIMD chunks with a scalar tail

- computes contiguous Float32 sum and mean through SIMD chunks with a scalar tail
   - Expected: a.sum_f32() equals `Float32.new(21.0f32)`
   - Expected: a.mean_f32() equals `Float32.new(3.5f32)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes contiguous Float32 sum and mean through SIMD chunks with a scalar tail")
val a = array_f32([
    Float32.new(1.0f32), Float32.new(2.0f32), Float32.new(3.0f32), Float32.new(4.0f32),
    Float32.new(5.0f32), Float32.new(6.0f32)])
expect(a.sum_f32()).to_equal(Float32.new(21.0f32))
expect(a.mean_f32()).to_equal(Float32.new(3.5f32))
```

</details>

#### reduces a strided slice using logical element order

- reduces a strided slice using logical element order
   - Expected: every_other.sum() equals `Float64.new(9.0)`
   - Expected: every_other.mean() equals `Float64.new(3.0)`
   - Expected: every_other.max() equals `Float64.new(5.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reduces a strided slice using logical element order")
val a = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0), Float64.new(5.0)])
val every_other = a.slice(Slice.new(Index.new(0), Index.new(5), Index.new(2)))
expect(every_other.sum()).to_equal(Float64.new(9.0))
expect(every_other.mean()).to_equal(Float64.new(3.0))
expect(every_other.max()).to_equal(Float64.new(5.0))
```

</details>

#### returns errors for empty mean/min/max/argmax

- returns errors for empty mean/min/max/argmax
   - Expected: empty.try_mean().is_err() is true
   - Expected: empty.try_min().is_err() is true
   - Expected: empty.try_max().is_err() is true
   - Expected: empty.try_argmax().is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns errors for empty mean/min/max/argmax")
val empty = array([])
expect(empty.try_mean().is_err()).to_equal(true)
expect(empty.try_min().is_err()).to_equal(true)
expect(empty.try_max().is_err()).to_equal(true)
expect(empty.try_argmax().is_err()).to_equal(true)
```

</details>

#### returns UnsupportedDType for Int64 reductions through Result APIs

- returns UnsupportedDType for Int64 reductions through Result APIs
   - Expected: ints.try_sum().is_err() is true
   - Expected: ints.try_sum_f32().is_err() is true
   - Expected: ints.try_mean_f32().is_err() is true
   - Expected: ints.try_min().is_err() is true
   - Expected: ints.try_max().is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns UnsupportedDType for Int64 reductions through Result APIs")
val ints = array_i64([Int64.new(1), Int64.new(2)])
expect(ints.try_sum().is_err()).to_equal(true)
expect(ints.try_sum_f32().is_err()).to_equal(true)
expect(ints.try_mean_f32().is_err()).to_equal(true)
expect(ints.try_min().is_err()).to_equal(true)
expect(ints.try_max().is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `f2a3c6728ca20efd454d7e7078cb8af80d5fc514ac426f98a1127bc8e3335ed9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f2a3c6728ca20efd454d7e7078cb8af80d5fc514ac426f98a1127bc8e3335ed9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f2a3c6728ca20efd454d7e7078cb8af80d5fc514ac426f98a1127bc8e3335ed9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/ndarray_reduction_spec.spl
mirror: doc/06_spec/feature/scilib/ndarray_reduction_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/ndarray_reduction_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/ndarray_reduction_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/ndarray_reduction_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes sum, mean, min, max, and argmax over a 1-D Float64 array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ndarray_reduction_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes contiguous Float64 sum and mean through SIMD chunks with a scalar tail' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ndarray_reduction_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes contiguous Float32 sum and mean through SIMD chunks with a scalar tail' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
