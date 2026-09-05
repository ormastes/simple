# linalg_simd_spec

> Purpose: Verify linalg SIMD helpers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# linalg_simd_spec

Purpose: Verify linalg SIMD helpers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/feature/scilib/linalg_simd_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Verify linalg SIMD helpers.
Audience: QA and feature maintainers reading this spec suite.

## Scenarios

### linalg SIMD helpers

#### computes a four-lane f64 dot product

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- computes a four-lane f64 dot product
- computes a four-lane f64 dot product
   - Expected: result.value equals `70.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes a four-lane f64 dot product")
step("computes a four-lane f64 dot product")
# @req: REQ-FEAT-SCILIB-LINALG-SIMD-SPEC-001
val result = simd_dot4_values(
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)],
    [Float64.new(5.0), Float64.new(6.0), Float64.new(7.0), Float64.new(8.0)]
).unwrap()
expect(result.value).to_equal(70.0)
```

</details>

#### matches the scalar lane calculation for four f64 values

- matches the scalar lane calculation for four f64 values
- matches the scalar lane calculation for four f64 values
   - Expected: simd_result.value equals `scalar_result`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches the scalar lane calculation for four f64 values")
step("matches the scalar lane calculation for four f64 values")
val left_values = [Float64.new(1.5), Float64.new(-2.0), Float64.new(0.5), Float64.new(4.0)]
val right_values = [Float64.new(2.0), Float64.new(3.0), Float64.new(-8.0), Float64.new(0.25)]
val simd_result = simd_dot4_values(left_values, right_values).unwrap()
val scalar_result = left_values[0].value * right_values[0].value
    + left_values[1].value * right_values[1].value
    + left_values[2].value * right_values[2].value
    + left_values[3].value * right_values[3].value
expect(simd_result.value).to_equal(scalar_result)
```

</details>

#### dispatches public dot through the four-lane f64 path

- dispatches public dot through the four-lane f64 path
- dispatches public dot through the four-lane f64 path
   - Expected: result.value equals `70.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("dispatches public dot through the four-lane f64 path")
step("dispatches public dot through the four-lane f64 path")
val result = dot(
    vector_from([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)]),
    vector_from([Float64.new(5.0), Float64.new(6.0), Float64.new(7.0), Float64.new(8.0)])
).unwrap()
expect(result.value).to_equal(70.0)
```

</details>

#### dispatches public dot through SIMD chunks with a scalar tail

- dispatches public dot through SIMD chunks with a scalar tail
- dispatches public dot through SIMD chunks with a scalar tail
   - Expected: result.value equals `910.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("dispatches public dot through SIMD chunks with a scalar tail")
step("dispatches public dot through SIMD chunks with a scalar tail")
val result = dot(
    vector_from([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]),
    vector_from([Float64.new(10.0), Float64.new(20.0), Float64.new(30.0), Float64.new(40.0), Float64.new(50.0), Float64.new(60.0)])
).unwrap()
expect(result.value).to_equal(910.0)
```

</details>

#### computes a tail-handled f64 dot helper

- computes a tail-handled f64 dot helper
- computes a tail-handled f64 dot helper
   - Expected: result.value equals `35.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes a tail-handled f64 dot helper")
step("computes a tail-handled f64 dot helper")
val result = simd_dot_values(
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0), Float64.new(5.0)],
    [Float64.new(5.0), Float64.new(4.0), Float64.new(3.0), Float64.new(2.0), Float64.new(1.0)]
).unwrap()
expect(result.value).to_equal(35.0)
```

</details>

#### rejects non-four-lane inputs

- rejects non-four-lane inputs
- rejects non-four-lane inputs
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects non-four-lane inputs")
step("rejects non-four-lane inputs")
val result = simd_dot4_values(
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]
)
expect(result.is_err()).to_equal(true)
```

</details>

#### computes a four-lane f64 axpy

- computes a four-lane f64 axpy
- computes a four-lane f64 axpy
   - Expected: result[0].value equals `7.0`
   - Expected: result[1].value equals `10.0`
   - Expected: result[2].value equals `13.0`
   - Expected: result[3].value equals `16.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes a four-lane f64 axpy")
step("computes a four-lane f64 axpy")
val result = simd_axpy4_values(
    Float64.new(2.0),
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)],
    [Float64.new(5.0), Float64.new(6.0), Float64.new(7.0), Float64.new(8.0)]
).unwrap()
expect(result[0].value).to_equal(7.0)
expect(result[1].value).to_equal(10.0)
expect(result[2].value).to_equal(13.0)
expect(result[3].value).to_equal(16.0)
```

</details>

#### dispatches public axpy through the four-lane f64 path

- dispatches public axpy through the four-lane f64 path
- dispatches public axpy through the four-lane f64 path
   - Expected: result.shape equals `Shape.new([Index.new(4)])`
   - Expected: result.get_f64(Index.new(0)).value equals `7.0`
   - Expected: result.get_f64(Index.new(1)).value equals `10.0`
   - Expected: result.get_f64(Index.new(2)).value equals `13.0`
   - Expected: result.get_f64(Index.new(3)).value equals `16.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("dispatches public axpy through the four-lane f64 path")
step("dispatches public axpy through the four-lane f64 path")
val result = try_axpy(
    Float64.new(2.0),
    vector_from([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)]),
    vector_from([Float64.new(5.0), Float64.new(6.0), Float64.new(7.0), Float64.new(8.0)])
).unwrap()
expect(result.shape).to_equal(Shape.new([Index.new(4)]))
expect(result.get_f64(Index.new(0)).value).to_equal(7.0)
expect(result.get_f64(Index.new(1)).value).to_equal(10.0)
expect(result.get_f64(Index.new(2)).value).to_equal(13.0)
expect(result.get_f64(Index.new(3)).value).to_equal(16.0)
```

</details>

#### dispatches public axpy through SIMD chunks with a scalar tail

- dispatches public axpy through SIMD chunks with a scalar tail
- dispatches public axpy through SIMD chunks with a scalar tail
   - Expected: result.shape equals `Shape.new([Index.new(6)])`
   - Expected: result.get_f64(Index.new(0)).value equals `12.0`
   - Expected: result.get_f64(Index.new(3)).value equals `48.0`
   - Expected: result.get_f64(Index.new(4)).value equals `60.0`
   - Expected: result.get_f64(Index.new(5)).value equals `72.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("dispatches public axpy through SIMD chunks with a scalar tail")
step("dispatches public axpy through SIMD chunks with a scalar tail")
val result = try_axpy(
    Float64.new(2.0),
    vector_from([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]),
    vector_from([Float64.new(10.0), Float64.new(20.0), Float64.new(30.0), Float64.new(40.0), Float64.new(50.0), Float64.new(60.0)])
).unwrap()
expect(result.shape).to_equal(Shape.new([Index.new(6)]))
expect(result.get_f64(Index.new(0)).value).to_equal(12.0)
expect(result.get_f64(Index.new(3)).value).to_equal(48.0)
expect(result.get_f64(Index.new(4)).value).to_equal(60.0)
expect(result.get_f64(Index.new(5)).value).to_equal(72.0)
```

</details>

#### computes a tail-handled f64 axpy helper

- computes a tail-handled f64 axpy helper
- computes a tail-handled f64 axpy helper
   - Expected: result[0].value equals `9.0`
   - Expected: result[3].value equals `36.0`
   - Expected: result[4].value equals `45.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes a tail-handled f64 axpy helper")
step("computes a tail-handled f64 axpy helper")
val result = simd_axpy_values(
    Float64.new(-1.0),
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0), Float64.new(5.0)],
    [Float64.new(10.0), Float64.new(20.0), Float64.new(30.0), Float64.new(40.0), Float64.new(50.0)]
).unwrap()
expect(result[0].value).to_equal(9.0)
expect(result[3].value).to_equal(36.0)
expect(result[4].value).to_equal(45.0)
```

</details>

#### matches scalar fma lane results for mixed-sign axpy

- matches scalar fma lane results for mixed-sign axpy
- matches scalar fma lane results for mixed-sign axpy
   - Expected: result[0].value equals `7.0`
   - Expected: result[1].value equals `7.0`
   - Expected: result[2].value equals `-2.75`
   - Expected: result[3].value equals `-9.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches scalar fma lane results for mixed-sign axpy")
step("matches scalar fma lane results for mixed-sign axpy")
val result = simd_axpy4_values(
    Float64.new(-1.5),
    [Float64.new(2.0), Float64.new(-4.0), Float64.new(0.5), Float64.new(8.0)],
    [Float64.new(10.0), Float64.new(1.0), Float64.new(-2.0), Float64.new(3.0)]
).unwrap()
expect(result[0].value).to_equal(7.0)
expect(result[1].value).to_equal(7.0)
expect(result[2].value).to_equal(-2.75)
expect(result[3].value).to_equal(-9.0)
```

</details>

#### rejects non-four-lane axpy inputs

- rejects non-four-lane axpy inputs
- rejects non-four-lane axpy inputs
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects non-four-lane axpy inputs")
step("rejects non-four-lane axpy inputs")
val result = simd_axpy4_values(
    Float64.new(2.0),
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)],
    [Float64.new(5.0), Float64.new(6.0), Float64.new(7.0)]
)
expect(result.is_err()).to_equal(true)
```

</details>

#### computes a four-lane f32 dot product

- computes a four-lane f32 dot product
- computes a four-lane f32 dot product
   - Expected: result.value equals `70.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes a four-lane f32 dot product")
step("computes a four-lane f32 dot product")
val result = simd_dot4_f32_values(
    [Float32.new(1.0f32), Float32.new(2.0f32), Float32.new(3.0f32), Float32.new(4.0f32)],
    [Float32.new(5.0f32), Float32.new(6.0f32), Float32.new(7.0f32), Float32.new(8.0f32)]
).unwrap()
expect(result.value).to_equal(70.0)
```

</details>

#### dispatches public f32 dot through SIMD chunks with a scalar tail

- dispatches public f32 dot through SIMD chunks with a scalar tail
- dispatches public f32 dot through SIMD chunks with a scalar tail
   - Expected: result.value equals `910.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("dispatches public f32 dot through SIMD chunks with a scalar tail")
step("dispatches public f32 dot through SIMD chunks with a scalar tail")
val result = dot_f32(
    vector_from_f32([Float32.new(1.0f32), Float32.new(2.0f32), Float32.new(3.0f32), Float32.new(4.0f32), Float32.new(5.0f32), Float32.new(6.0f32)]),
    vector_from_f32([Float32.new(10.0f32), Float32.new(20.0f32), Float32.new(30.0f32), Float32.new(40.0f32), Float32.new(50.0f32), Float32.new(60.0f32)])
).unwrap()
expect(result.value).to_equal(910.0)
```

</details>

#### computes a tail-handled f32 dot helper

- computes a tail-handled f32 dot helper
- computes a tail-handled f32 dot helper
   - Expected: result.value equals `35.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes a tail-handled f32 dot helper")
step("computes a tail-handled f32 dot helper")
val result = simd_dot_f32_values(
    [Float32.new(1.0f32), Float32.new(2.0f32), Float32.new(3.0f32), Float32.new(4.0f32), Float32.new(5.0f32)],
    [Float32.new(5.0f32), Float32.new(4.0f32), Float32.new(3.0f32), Float32.new(2.0f32), Float32.new(1.0f32)]
).unwrap()
expect(result.value).to_equal(35.0)
```

</details>

#### computes a four-lane f32 axpy

- computes a four-lane f32 axpy
- computes a four-lane f32 axpy
   - Expected: result[0].value equals `7.0`
   - Expected: result[1].value equals `10.0`
   - Expected: result[2].value equals `13.0`
   - Expected: result[3].value equals `16.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes a four-lane f32 axpy")
step("computes a four-lane f32 axpy")
val result = simd_axpy4_f32_values(
    Float32.new(2.0f32),
    [Float32.new(1.0f32), Float32.new(2.0f32), Float32.new(3.0f32), Float32.new(4.0f32)],
    [Float32.new(5.0f32), Float32.new(6.0f32), Float32.new(7.0f32), Float32.new(8.0f32)]
).unwrap()
expect(result[0].value).to_equal(7.0)
expect(result[1].value).to_equal(10.0)
expect(result[2].value).to_equal(13.0)
expect(result[3].value).to_equal(16.0)
```

</details>

#### dispatches public f32 axpy through SIMD chunks with a scalar tail

- dispatches public f32 axpy through SIMD chunks with a scalar tail
- dispatches public f32 axpy through SIMD chunks with a scalar tail
   - Expected: result.shape equals `Shape.new([Index.new(6)])`
   - Expected: result.get_f32(Index.new(0)).value equals `12.0`
   - Expected: result.get_f32(Index.new(3)).value equals `48.0`
   - Expected: result.get_f32(Index.new(4)).value equals `60.0`
   - Expected: result.get_f32(Index.new(5)).value equals `72.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("dispatches public f32 axpy through SIMD chunks with a scalar tail")
step("dispatches public f32 axpy through SIMD chunks with a scalar tail")
val result = try_axpy_f32(
    Float32.new(2.0f32),
    vector_from_f32([Float32.new(1.0f32), Float32.new(2.0f32), Float32.new(3.0f32), Float32.new(4.0f32), Float32.new(5.0f32), Float32.new(6.0f32)]),
    vector_from_f32([Float32.new(10.0f32), Float32.new(20.0f32), Float32.new(30.0f32), Float32.new(40.0f32), Float32.new(50.0f32), Float32.new(60.0f32)])
).unwrap()
expect(result.shape).to_equal(Shape.new([Index.new(6)]))
expect(result.get_f32(Index.new(0)).value).to_equal(12.0)
expect(result.get_f32(Index.new(3)).value).to_equal(48.0)
expect(result.get_f32(Index.new(4)).value).to_equal(60.0)
expect(result.get_f32(Index.new(5)).value).to_equal(72.0)
```

</details>

#### rejects mismatched f32 linalg inputs

- rejects mismatched f32 linalg inputs
- rejects mismatched f32 linalg inputs
   - Expected: dot_result.is_err() is true
   - Expected: axpy_result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects mismatched f32 linalg inputs")
step("rejects mismatched f32 linalg inputs")
val dot_result = dot_f32(
    vector_from_f32([Float32.new(1.0f32), Float32.new(2.0f32)]),
    vector_from_f32([Float32.new(3.0f32)])
)
val axpy_result = try_axpy_f32(
    Float32.new(2.0f32),
    vector_from_f32([Float32.new(1.0f32), Float32.new(2.0f32)]),
    vector_from_f32([Float32.new(3.0f32)])
)
expect(dot_result.is_err()).to_equal(true)
expect(axpy_result.is_err()).to_equal(true)
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
- `REQ-FEAT-SCILIB-LINALG-SIMD-SPEC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bb23cf8bb79bcdeb9b8ce4267635c9c584081aa49c1f1ce695a42c148127f04b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bb23cf8bb79bcdeb9b8ce4267635c9c584081aa49c1f1ce695a42c148127f04b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bb23cf8bb79bcdeb9b8ce4267635c9c584081aa49c1f1ce695a42c148127f04b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/scilib/linalg_simd_spec.spl
mirror: doc/06_spec/feature/scilib/linalg_simd_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/linalg_simd_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/linalg_simd_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/linalg_simd_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 34 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/scilib/linalg_simd_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes a four-lane f64 dot product' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/linalg_simd_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the scalar lane calculation for four f64 values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/linalg_simd_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches public dot through the four-lane f64 path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
