# Linalg Backend Diagnostics Specification

> Tests covering linalg backend diagnostics.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Linalg Backend Diagnostics Specification

## Scenarios

### linalg backend diagnostics

#### reports the configured backend without requiring native libraries

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports the configured backend without requiring native libraries
   - Expected: status.selected equals `mock`
   - Expected: status.available is true
   - Expected: status.real_native is false
   - Expected: required.selected equals `cuda`
   - Expected: name equals `cuda`
   - Expected: false is true
   - Expected: required.selected equals `pytorch`
   - Expected: name equals `status.requested`
   - Expected: false is true
   - Expected: status.selected equals `scalar`
   - Expected: status.available is true
   - Expected: required.selected equals `openblas`
   - Expected: name equals `openblas`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reports the configured backend without requiring native libraries")
val status = linalg_backend_status()
if status.requested == "mock":
    expect(status.selected).to_equal("mock")
    expect(status.available).to_equal(true)
    expect(status.real_native).to_equal(false)
if status.requested == "cuda":
    match require_linalg_backend("cuda"):
        case Ok(required):
            expect(required.selected).to_equal("cuda")
        case Err(BackendError.BackendUnavailable(name)):
            expect(name).to_equal("cuda")
        case _:
            expect(false).to_equal(true)
if status.requested == "torch" or status.requested == "pytorch":
    match require_linalg_backend(status.requested):
        case Ok(required):
            expect(required.selected).to_equal("pytorch")
        case Err(BackendError.BackendUnavailable(name)):
            expect(name).to_equal(status.requested)
        case _:
            expect(false).to_equal(true)
if status.requested == "auto":
    expect(status.selected).to_equal("scalar")
    expect(status.available).to_equal(true)
if status.requested == "openblas":
    match require_linalg_backend("openblas"):
        case Ok(required):
            expect(required.selected).to_equal("openblas")
        case Err(BackendError.BackendUnavailable(name)):
            expect(name).to_equal("openblas")
        case _:
            expect(false).to_equal(true)
```

</details>

#### returns typed unavailable errors for optional accelerator backends

- returns typed unavailable errors for optional accelerator backends
   - Expected: status.selected equals `openblas`
   - Expected: status.available is true
   - Expected: name equals `openblas`
   - Expected: false is true
   - Expected: name equals `cuda`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns typed unavailable errors for optional accelerator backends")
val openblas = require_linalg_backend("openblas")
match openblas:
    case Ok(status):
        expect(status.selected).to_equal("openblas")
        expect(status.available).to_equal(true)
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("openblas")
    case _:
        expect(false).to_equal(true)

val cuda = require_linalg_backend("cuda")
match cuda:
    case Err(BackendError.BackendUnavailable(name)):
        expect(name).to_equal("cuda")
    case _:
        expect(false).to_equal(true)
```

</details>

#### returns typed missing-symbol errors for backend symbol probes

- returns typed missing-symbol errors for backend symbol probes
   - Expected: symbol equals `rt_blas_dgemm`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns typed missing-symbol errors for backend symbol probes")
val missing = check_linalg_symbol("mock", "rt_blas_dgemm", false)
match missing:
    case Err(BackendError.MissingRuntimeSymbol(symbol)):
        expect(symbol).to_equal("rt_blas_dgemm")
    case _:
        expect(false).to_equal(true)
```

</details>

#### returns typed unsupported errors for unknown backend names

- returns typed unsupported errors for unknown backend names
   - Expected: name equals `not-a-backend`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns typed unsupported errors for unknown backend names")
val unknown = require_linalg_backend("not-a-backend")
match unknown:
    case Err(BackendError.UnsupportedBackend(name)):
        expect(name).to_equal("not-a-backend")
    case _:
        expect(false).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/feature/scilib/linalg_backend_diagnostics_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering linalg backend diagnostics.
- linalg backend diagnostics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `78ed5f4a942d69dfa18396a2f6678810cf4bde1b620597c05d3342057ec31d9b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `78ed5f4a942d69dfa18396a2f6678810cf4bde1b620597c05d3342057ec31d9b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `78ed5f4a942d69dfa18396a2f6678810cf4bde1b620597c05d3342057ec31d9b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/linalg_backend_diagnostics_spec.spl
mirror: doc/06_spec/feature/scilib/linalg_backend_diagnostics_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/linalg_backend_diagnostics_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/linalg_backend_diagnostics_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/linalg_backend_diagnostics_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the configured backend without requiring native libraries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/linalg_backend_diagnostics_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns typed unavailable errors for optional accelerator backends' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/linalg_backend_diagnostics_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns typed missing-symbol errors for backend symbol probes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
