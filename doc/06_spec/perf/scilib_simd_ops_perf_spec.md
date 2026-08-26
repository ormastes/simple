# Scilib Simd Ops Perf Specification

> Tests covering science SIMD operation performance probe.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scilib Simd Ops Perf Specification

## Scenarios

### science SIMD operation performance probe

#### records public SIMD-backed operation timings

**Manual warnings:**
- invalid manual visibility metadata: # @manual scilib SIMD performance evidence (expected show, folded, detail, or skip)


- time dot/axpy/add/sum/square/abs/scalar ops on fixed fixtures
   - Expected: result.value equals `120.0`
   - Expected: result.get_f64(Index.new(7)).value equals `17.0`
   - Expected: result.value equals `120.0`
   - Expected: result.get_f32(Index.new(7)).value equals `17.0`
   - Expected: result.get_f64(Index.new(7)).value equals `9.0`
   - Expected: result.value equals `36.0`
   - Expected: result.get_f64(Index.new(7)).value equals `64.0`
   - Expected: result.get_f64(Index.new(7)).value equals `8.0`
   - Expected: result.get_f64(Index.new(7)).value equals `16.0`
   - Expected: result.value equals `36.0`
   - Expected: result.get_f32(Index.new(7)).value equals `16.0`
   - Expected: result.get_f32(Index.new(7)).value equals `4.0`
   - Expected: result.get_f32(Index.new(7)).value equals `64.0`
   - Expected: result.get_f32(Index.new(7)).value equals `8.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 126 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-SCILIB-SIMD
# oracle: all expected numeric values below are the closed-form
# results of the fixed 1..8 / 8..1 fixtures (dot=120, sum=36, etc).
step("time dot/axpy/add/sum/square/abs/scalar ops on fixed fixtures")
val iterations = 1000
val f64_left = vector_from([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0), Float64.new(5.0), Float64.new(6.0), Float64.new(7.0), Float64.new(8.0)])
val f64_right = vector_from([Float64.new(8.0), Float64.new(7.0), Float64.new(6.0), Float64.new(5.0), Float64.new(4.0), Float64.new(3.0), Float64.new(2.0), Float64.new(1.0)])
val f32_left = vector_from_f32([Float32.new(1.0), Float32.new(2.0), Float32.new(3.0), Float32.new(4.0), Float32.new(5.0), Float32.new(6.0), Float32.new(7.0), Float32.new(8.0)])
val f32_right = vector_from_f32([Float32.new(8.0), Float32.new(7.0), Float32.new(6.0), Float32.new(5.0), Float32.new(4.0), Float32.new(3.0), Float32.new(2.0), Float32.new(1.0)])

var i = 0
var start = rt_time_now_nanos()
while i < iterations:
    val result = dot(f64_left, f64_right).unwrap()
    expect(result.value).to_equal(120.0)
    i = i + 1
_report("simd_f64_dot_avg_ns", iterations, rt_time_now_nanos() - start)

i = 0
start = rt_time_now_nanos()
while i < iterations:
    val result = try_axpy(Float64.new(2.0), f64_left, f64_right).unwrap()
    expect(result.get_f64(Index.new(7)).value).to_equal(17.0)
    i = i + 1
_report("simd_f64_axpy_avg_ns", iterations, rt_time_now_nanos() - start)

i = 0
start = rt_time_now_nanos()
while i < iterations:
    val result = dot_f32(f32_left, f32_right).unwrap()
    expect(result.value).to_equal(120.0)
    i = i + 1
_report("simd_f32_dot_avg_ns", iterations, rt_time_now_nanos() - start)

i = 0
start = rt_time_now_nanos()
while i < iterations:
    val result = try_axpy_f32(Float32.new(2.0), f32_left, f32_right).unwrap()
    expect(result.get_f32(Index.new(7)).value).to_equal(17.0)
    i = i + 1
_report("simd_f32_axpy_avg_ns", iterations, rt_time_now_nanos() - start)

i = 0
start = rt_time_now_nanos()
while i < iterations:
    val result = f64_left.add(f64_right)
    expect(result.get_f64(Index.new(7)).value).to_equal(9.0)
    i = i + 1
_report("simd_ndarray_f64_add_avg_ns", iterations, rt_time_now_nanos() - start)

i = 0
start = rt_time_now_nanos()
while i < iterations:
    val result = f64_left.sum()
    expect(result.value).to_equal(36.0)
    i = i + 1
_report("simd_ndarray_f64_sum_avg_ns", iterations, rt_time_now_nanos() - start)

i = 0
start = rt_time_now_nanos()
while i < iterations:
    val result = f64_left.square()
    expect(result.get_f64(Index.new(7)).value).to_equal(64.0)
    i = i + 1
_report("simd_ndarray_f64_square_avg_ns", iterations, rt_time_now_nanos() - start)

i = 0
start = rt_time_now_nanos()
while i < iterations:
    val result = f64_left.abs()
    expect(result.get_f64(Index.new(7)).value).to_equal(8.0)
    i = i + 1
_report("simd_ndarray_f64_abs_avg_ns", iterations, rt_time_now_nanos() - start)

i = 0
start = rt_time_now_nanos()
while i < iterations:
    val result = f64_left.mul_scalar(Float64.new(2.0))
    expect(result.get_f64(Index.new(7)).value).to_equal(16.0)
    i = i + 1
_report("simd_ndarray_f64_scalar_mul_avg_ns", iterations, rt_time_now_nanos() - start)

i = 0
start = rt_time_now_nanos()
while i < iterations:
    val f32_sum_v = vector_from_f32([Float32.new(1.0), Float32.new(2.0), Float32.new(3.0), Float32.new(4.0), Float32.new(5.0), Float32.new(6.0), Float32.new(7.0), Float32.new(8.0)])
    val result = f32_sum_v.sum_f32()
    expect(result.value).to_equal(36.0)
    i = i + 1
_report("simd_ndarray_f32_sum_avg_ns", iterations, rt_time_now_nanos() - start)

i = 0
start = rt_time_now_nanos()
while i < iterations:
    val f32_mul_v = vector_from_f32([Float32.new(1.0), Float32.new(2.0), Float32.new(3.0), Float32.new(4.0), Float32.new(5.0), Float32.new(6.0), Float32.new(7.0), Float32.new(8.0)])
    val result = f32_mul_v.mul_scalar_f32(Float32.new(2.0))
    expect(result.get_f32(Index.new(7)).value).to_equal(16.0)
    i = i + 1
_report("simd_ndarray_f32_scalar_mul_avg_ns", iterations, rt_time_now_nanos() - start)

i = 0
start = rt_time_now_nanos()
while i < iterations:
    val f32_div_v = vector_from_f32([Float32.new(1.0), Float32.new(2.0), Float32.new(3.0), Float32.new(4.0), Float32.new(5.0), Float32.new(6.0), Float32.new(7.0), Float32.new(8.0)])
    val result = f32_div_v.div_scalar_f32(Float32.new(2.0))
    expect(result.get_f32(Index.new(7)).value).to_equal(4.0)
    i = i + 1
_report("simd_ndarray_f32_scalar_div_avg_ns", iterations, rt_time_now_nanos() - start)

i = 0
start = rt_time_now_nanos()
while i < iterations:
    val f32_sq_v = vector_from_f32([Float32.new(1.0), Float32.new(2.0), Float32.new(3.0), Float32.new(4.0), Float32.new(5.0), Float32.new(6.0), Float32.new(7.0), Float32.new(8.0)])
    val result = f32_sq_v.square_f32()
    expect(result.get_f32(Index.new(7)).value).to_equal(64.0)
    i = i + 1
_report("simd_ndarray_f32_square_avg_ns", iterations, rt_time_now_nanos() - start)

i = 0
start = rt_time_now_nanos()
while i < iterations:
    val f32_abs_v = vector_from_f32([Float32.new(1.0), Float32.new(2.0), Float32.new(3.0), Float32.new(4.0), Float32.new(5.0), Float32.new(6.0), Float32.new(7.0), Float32.new(8.0)])
    val result = f32_abs_v.abs_f32()
    expect(result.get_f32(Index.new(7)).value).to_equal(8.0)
    i = i + 1
_report("simd_ndarray_f32_abs_avg_ns", iterations, rt_time_now_nanos() - start)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Performance |
| Status | Active |
| Source | `test/perf/scilib_simd_ops_perf_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering science SIMD operation performance probe.
- science SIMD operation performance probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-PERF-SCILIB-SIMD`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8fea65b602c6a10a76a9281507ae62e655c5b4827c71654a378b4fb5de9f6418`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8fea65b602c6a10a76a9281507ae62e655c5b4827c71654a378b4fb5de9f6418`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8fea65b602c6a10a76a9281507ae62e655c5b4827c71654a378b4fb5de9f6418`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/perf/scilib_simd_ops_perf_spec.spl
mirror: doc/06_spec/perf/scilib_simd_ops_perf_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/perf/scilib_simd_ops_perf_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/perf/scilib_simd_ops_perf_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/perf/scilib_simd_ops_perf_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/perf/scilib_simd_ops_perf_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 14 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/perf/scilib_simd_ops_perf_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records public SIMD-backed operation timings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
