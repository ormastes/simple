# Linalg OpenBLAS Backend Specification

> NFR-SCILIB-B-001, NFR-SCILIB-B-002, NFR-SCILIB-B-004

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Linalg OpenBLAS Backend Specification

NFR-SCILIB-B-001, NFR-SCILIB-B-002, NFR-SCILIB-B-004

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | REQ-SCILIB-B-001, REQ-SCILIB-B-002, REQ-SCILIB-B-003, REQ-SCILIB-B-004, |
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/scilib/linalg_openblas_backend_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

NFR-SCILIB-B-001, NFR-SCILIB-B-002, NFR-SCILIB-B-004

Validates the dynamic OpenBLAS/LAPACKE adapter. The existing scalar public APIs
keep their signatures and fall back to scalar behavior when the native shim is
unavailable.

## Scenarios

### linalg OpenBLAS dynamic backend

#### reports either an available OpenBLAS backend or a typed unavailable error

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports either an available OpenBLAS backend or a typed unavailable error
   - Expected: status.selected equals `openblas`
   - Expected: status.real_native is true
   - Expected: name equals `openblas`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports either an available OpenBLAS backend or a typed unavailable error")
val required = require_linalg_backend("openblas")
match required:
    case Ok(status):
        expect(status.selected).to_equal("openblas")
        expect(status.real_native).to_equal(true)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("openblas")
    case _:
        fail("unexpected checked result branch")
```

</details>

#### matches scalar dot when the OpenBLAS shim is available

- matches scalar dot when the OpenBLAS shim is available
   - Expected: value equals `dot(left, right).unwrap()`
   - Expected: name equals `openblas`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches scalar dot when the OpenBLAS shim is available")
val left = vector_from([Float64.new(1.5), Float64.new(-2.0), Float64.new(3.25), Float64.new(4.0)])
val right = vector_from([Float64.new(2.0), Float64.new(5.0), Float64.new(-1.0), Float64.new(0.5)])
val result = openblas_dot(left, right)
match result:
    case Ok(value):
        expect(value).to_equal(dot(left, right).unwrap())
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("openblas")
    case _:
        fail("unexpected checked result branch")
```

</details>

#### matches scalar axpy when the OpenBLAS shim is available

- matches scalar axpy when the OpenBLAS shim is available
   - Expected: value.get_f64(Index.new(0)) equals `scalar.get_f64(Index.new(0))`
   - Expected: value.get_f64(Index.new(3)) equals `scalar.get_f64(Index.new(3))`
   - Expected: name equals `openblas`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches scalar axpy when the OpenBLAS shim is available")
val x = vector_from([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)])
val y = vector_from([Float64.new(5.0), Float64.new(6.0), Float64.new(7.0), Float64.new(8.0)])
val result = openblas_axpy(Float64.new(2.0), x, y)
match result:
    case Ok(value):
        val scalar = try_axpy(Float64.new(2.0), x, y).unwrap()
        expect(value.get_f64(Index.new(0))).to_equal(scalar.get_f64(Index.new(0)))
        expect(value.get_f64(Index.new(3))).to_equal(scalar.get_f64(Index.new(3)))
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("openblas")
    case _:
        fail("unexpected checked result branch")
```

</details>

#### matches scalar gemm when the OpenBLAS shim is available

- matches scalar gemm when the OpenBLAS shim is available
   - Expected: value.get_f64_at([Index.new(0), Index.new(0)]) equals `scalar.get_f64_at([Index.new(0), Index.new(0)])`
   - Expected: value.get_f64_at([Index.new(1), Index.new(1)]) equals `scalar.get_f64_at([Index.new(1), Index.new(1)])`
   - Expected: name equals `openblas`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches scalar gemm when the OpenBLAS shim is available")
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]])
val b = matrix_from_rows([
    [Float64.new(7.0), Float64.new(8.0)],
    [Float64.new(9.0), Float64.new(10.0)],
    [Float64.new(11.0), Float64.new(12.0)]])
val c_in = full_matrix(Index.new(2), Index.new(2), Float64.new(1.0))
val result = openblas_gemm(Float64.new(2.0), a, b, Float64.new(3.0), c_in)
match result:
    case Ok(value):
        val scalar = gemm(Float64.new(2.0), a, b, Float64.new(3.0), c_in)
        expect(value.get_f64_at([Index.new(0), Index.new(0)])).to_equal(scalar.get_f64_at([Index.new(0), Index.new(0)]))
        expect(value.get_f64_at([Index.new(1), Index.new(1)])).to_equal(scalar.get_f64_at([Index.new(1), Index.new(1)]))
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("openblas")
    case _:
        fail("unexpected checked result branch")
```

</details>

#### matches scalar solve when the OpenBLAS shim is available

- matches scalar solve when the OpenBLAS shim is available
   - Expected: value.get_f64(Index.new(0)) equals `scalar.get_f64(Index.new(0))`
   - Expected: value.get_f64(Index.new(1)) equals `scalar.get_f64(Index.new(1))`
   - Expected: value.get_f64(Index.new(2)) equals `scalar.get_f64(Index.new(2))`
   - Expected: name equals `openblas`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches scalar solve when the OpenBLAS shim is available")
val a = matrix_from_rows([
    [Float64.new(2.0), Float64.new(0.0), Float64.new(0.0)],
    [Float64.new(1.0), Float64.new(2.0), Float64.new(0.0)],
    [Float64.new(1.0), Float64.new(1.0), Float64.new(3.0)]])
val b = vector_from([Float64.new(2.0), Float64.new(5.0), Float64.new(14.0)])
val result = openblas_solve(a, b)
match result:
    case Ok(value):
        val scalar = solve(a, b).unwrap()
        expect(value.get_f64(Index.new(0))).to_equal(scalar.get_f64(Index.new(0)))
        expect(value.get_f64(Index.new(1))).to_equal(scalar.get_f64(Index.new(1)))
        expect(value.get_f64(Index.new(2))).to_equal(scalar.get_f64(Index.new(2)))
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("openblas")
    case _:
        fail("unexpected checked result branch")
```

</details>

#### preserves public scalar fallback when OpenBLAS is requested but unavailable

- preserves public scalar fallback when OpenBLAS is requested but unavailable
   - Expected: dot(left, right).unwrap().value equals `32.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves public scalar fallback when OpenBLAS is requested but unavailable")
val left = vector_from([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
val right = vector_from([Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)])
expect(dot(left, right).unwrap().value).to_equal(32.0)
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-SCILIB-B-001`
- `REQ-SCILIB-B-002`
- `REQ-SCILIB-B-003`
- `REQ-SCILIB-B-004`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1365aa3cb69d6a16b75c7d01d7327cdd4cf0529df56ba6e9557261b40c973aff`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1365aa3cb69d6a16b75c7d01d7327cdd4cf0529df56ba6e9557261b40c973aff`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1365aa3cb69d6a16b75c7d01d7327cdd4cf0529df56ba6e9557261b40c973aff`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/feature/scilib/linalg_openblas_backend_spec.spl
mirror: doc/06_spec/03_system/feature/scilib/linalg_openblas_backend_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/scilib/linalg_openblas_backend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/scilib/linalg_openblas_backend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/scilib/linalg_openblas_backend_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/scilib/linalg_openblas_backend_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports either an available OpenBLAS backend or a typed unavailable error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/scilib/linalg_openblas_backend_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches scalar dot when the OpenBLAS shim is available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/scilib/linalg_openblas_backend_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches scalar axpy when the OpenBLAS shim is available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
