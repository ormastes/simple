# NDArray SIMD Operations Specification

> Purpose: Verify NDArray SIMD elementwise ops — F64.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NDArray SIMD Operations Specification

Purpose: Verify NDArray SIMD elementwise ops — F64.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | scilib-ndarray-simd |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Draft |
| Plan | doc/03_plan/agent_tasks/scilib_port_ndarray.md |
| Design | doc/05_design/scilib_port_architecture.md |
| Source | `test/feature/scilib/ndarray_simd_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Verify NDArray SIMD elementwise ops — F64.
Audience: QA and feature maintainers reading this spec suite.

## Scenarios

### NDArray SIMD elementwise ops — F64

#### add on 6-element F64 arrays produces correct chunk+tail results

- add on 6-element F64 arrays produces correct chunk+tail results
- add on 6-element F64 arrays produces correct chunk+tail results
   - Expected: r.shape equals `Shape.new([Index.new(6)])`
   - Expected: r.get(Index.new(0)) equals `Float64.new(11.0)`
   - Expected: r.get(Index.new(3)) equals `Float64.new(44.0)`
   - Expected: r.get(Index.new(4)) equals `Float64.new(55.0)`
   - Expected: r.get(Index.new(5)) equals `Float64.new(66.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("add on 6-element F64 arrays produces correct chunk+tail results")
step("add on 6-element F64 arrays produces correct chunk+tail results")
# @req: REQ-FEAT-SCILIB-NDARRAY-SIMD-SPEC-001
val a = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0),
               Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)])
val b = array([Float64.new(10.0), Float64.new(20.0), Float64.new(30.0),
               Float64.new(40.0), Float64.new(50.0), Float64.new(60.0)])
val r = a.add(b)
expect(r.shape).to_equal(Shape.new([Index.new(6)]))
expect(r.get(Index.new(0))).to_equal(Float64.new(11.0))
expect(r.get(Index.new(3))).to_equal(Float64.new(44.0))
expect(r.get(Index.new(4))).to_equal(Float64.new(55.0))
expect(r.get(Index.new(5))).to_equal(Float64.new(66.0))
```

</details>

#### mul on 6-element F64 arrays produces correct chunk+tail results

- mul on 6-element F64 arrays produces correct chunk+tail results
- mul on 6-element F64 arrays produces correct chunk+tail results
   - Expected: r.get(Index.new(0)) equals `Float64.new(2.0)`
   - Expected: r.get(Index.new(4)) equals `Float64.new(10.0)`
   - Expected: r.get(Index.new(5)) equals `Float64.new(12.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("mul on 6-element F64 arrays produces correct chunk+tail results")
step("mul on 6-element F64 arrays produces correct chunk+tail results")
val a = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0),
               Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)])
val b = array([Float64.new(2.0), Float64.new(2.0), Float64.new(2.0),
               Float64.new(2.0), Float64.new(2.0), Float64.new(2.0)])
val r = a.mul(b)
expect(r.get(Index.new(0))).to_equal(Float64.new(2.0))
expect(r.get(Index.new(4))).to_equal(Float64.new(10.0))
expect(r.get(Index.new(5))).to_equal(Float64.new(12.0))
```

</details>

#### mul_scalar on 6-element F64 array uses SIMD broadcast path

- mul_scalar on 6-element F64 array uses SIMD broadcast path
- mul_scalar on 6-element F64 array uses SIMD broadcast path
   - Expected: r.get(Index.new(0)) equals `Float64.new(6.0)`
   - Expected: r.get(Index.new(4)) equals `Float64.new(30.0)`
   - Expected: r.get(Index.new(5)) equals `Float64.new(36.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("mul_scalar on 6-element F64 array uses SIMD broadcast path")
step("mul_scalar on 6-element F64 array uses SIMD broadcast path")
val a = array([Float64.new(2.0), Float64.new(4.0), Float64.new(6.0),
               Float64.new(8.0), Float64.new(10.0), Float64.new(12.0)])
val r = a.mul_scalar(Float64.new(3.0))
expect(r.get(Index.new(0))).to_equal(Float64.new(6.0))
expect(r.get(Index.new(4))).to_equal(Float64.new(30.0))
expect(r.get(Index.new(5))).to_equal(Float64.new(36.0))
```

</details>

### NDArray SIMD elementwise ops — F32

#### add on 6-element F32 arrays produces correct results

- add on 6-element F32 arrays produces correct results
- add on 6-element F32 arrays produces correct results
   - Expected: r.dtype equals `DType.F32`
   - Expected: r.shape equals `Shape.new([Index.new(6)])`
   - Expected: r.get(Index.new(0)) equals `Float32.new(11.0f32)`
   - Expected: r.get(Index.new(3)) equals `Float32.new(44.0f32)`
   - Expected: r.get(Index.new(5)) equals `Float32.new(66.0f32)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("add on 6-element F32 arrays produces correct results")
step("add on 6-element F32 arrays produces correct results")
val a = array_f32([Float32.new(1.0f32), Float32.new(2.0f32), Float32.new(3.0f32),
                   Float32.new(4.0f32), Float32.new(5.0f32), Float32.new(6.0f32)])
val b = array_f32([Float32.new(10.0f32), Float32.new(20.0f32), Float32.new(30.0f32),
                   Float32.new(40.0f32), Float32.new(50.0f32), Float32.new(60.0f32)])
val r = a.add(b)
expect(r.dtype).to_equal(DType.F32)
expect(r.shape).to_equal(Shape.new([Index.new(6)]))
expect(r.get(Index.new(0))).to_equal(Float32.new(11.0f32))
expect(r.get(Index.new(3))).to_equal(Float32.new(44.0f32))
expect(r.get(Index.new(5))).to_equal(Float32.new(66.0f32))
```

</details>

#### mul on 6-element F32 arrays produces correct results

- mul on 6-element F32 arrays produces correct results
- mul on 6-element F32 arrays produces correct results
   - Expected: r.dtype equals `DType.F32`
   - Expected: r.get(Index.new(0)) equals `Float32.new(2.0f32)`
   - Expected: r.get(Index.new(5)) equals `Float32.new(12.0f32)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("mul on 6-element F32 arrays produces correct results")
step("mul on 6-element F32 arrays produces correct results")
val a = array_f32([Float32.new(1.0f32), Float32.new(2.0f32), Float32.new(3.0f32),
                   Float32.new(4.0f32), Float32.new(5.0f32), Float32.new(6.0f32)])
val b = array_f32([Float32.new(2.0f32), Float32.new(2.0f32), Float32.new(2.0f32),
                   Float32.new(2.0f32), Float32.new(2.0f32), Float32.new(2.0f32)])
val r = a.mul(b)
expect(r.dtype).to_equal(DType.F32)
expect(r.get(Index.new(0))).to_equal(Float32.new(2.0f32))
expect(r.get(Index.new(5))).to_equal(Float32.new(12.0f32))
```

</details>

### NDArray SIMD linalg ops — dot and axpy

#### dot on 6-element F64 vectors produces correct result

- dot on 6-element F64 vectors produces correct result
- dot on 6-element F64 vectors produces correct result
   - Expected: result.value equals `910.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("dot on 6-element F64 vectors produces correct result")
step("dot on 6-element F64 vectors produces correct result")
val result = dot(
    vector_from([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0),
                 Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]),
    vector_from([Float64.new(10.0), Float64.new(20.0), Float64.new(30.0),
                 Float64.new(40.0), Float64.new(50.0), Float64.new(60.0)])
).unwrap()
expect(result.value).to_equal(910.0)
```

</details>

#### try_axpy on 6-element F64 vectors produces correct result

- try_axpy on 6-element F64 vectors produces correct result
- try_axpy on 6-element F64 vectors produces correct result
   - Expected: result.shape equals `Shape.new([Index.new(6)])`
   - Expected: result.get_f64(Index.new(0)).value equals `12.0`
   - Expected: result.get_f64(Index.new(3)).value equals `48.0`
   - Expected: result.get_f64(Index.new(5)).value equals `72.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("try_axpy on 6-element F64 vectors produces correct result")
step("try_axpy on 6-element F64 vectors produces correct result")
val result = try_axpy(
    Float64.new(2.0),
    vector_from([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0),
                 Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]),
    vector_from([Float64.new(10.0), Float64.new(20.0), Float64.new(30.0),
                 Float64.new(40.0), Float64.new(50.0), Float64.new(60.0)])
).unwrap()
expect(result.shape).to_equal(Shape.new([Index.new(6)]))
expect(result.get_f64(Index.new(0)).value).to_equal(12.0)
expect(result.get_f64(Index.new(3)).value).to_equal(48.0)
expect(result.get_f64(Index.new(5)).value).to_equal(72.0)
```

</details>

#### dot_f32 on 6-element F32 vectors produces correct result

- dot_f32 on 6-element F32 vectors produces correct result
- dot_f32 on 6-element F32 vectors produces correct result
   - Expected: result.value equals `910.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("dot_f32 on 6-element F32 vectors produces correct result")
step("dot_f32 on 6-element F32 vectors produces correct result")
val result = dot_f32(
    vector_from_f32([Float32.new(1.0f32), Float32.new(2.0f32), Float32.new(3.0f32),
                     Float32.new(4.0f32), Float32.new(5.0f32), Float32.new(6.0f32)]),
    vector_from_f32([Float32.new(10.0f32), Float32.new(20.0f32), Float32.new(30.0f32),
                     Float32.new(40.0f32), Float32.new(50.0f32), Float32.new(60.0f32)])
).unwrap()
expect(result.value).to_equal(910.0)
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

- **Plan:** `doc/03_plan/agent_tasks/scilib_port_ndarray.md`
- **Design:** `doc/05_design/scilib_port_architecture.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
- `REQ-FEAT-SCILIB-NDARRAY-SIMD-SPEC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `84f3a26b9adfee88b5a23125f9eb52e2b7739555d5419a8f914729f0ffd75cd4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `84f3a26b9adfee88b5a23125f9eb52e2b7739555d5419a8f914729f0ffd75cd4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `84f3a26b9adfee88b5a23125f9eb52e2b7739555d5419a8f914729f0ffd75cd4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/scilib/ndarray_simd_spec.spl
mirror: doc/06_spec/feature/scilib/ndarray_simd_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/ndarray_simd_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/ndarray_simd_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/ndarray_simd_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/scilib/ndarray_simd_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'add on 6-element F64 arrays produces correct chunk+tail results' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ndarray_simd_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mul on 6-element F64 arrays produces correct chunk+tail results' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ndarray_simd_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mul_scalar on 6-element F64 array uses SIMD broadcast path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
