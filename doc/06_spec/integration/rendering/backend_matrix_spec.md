# Backend Matrix Specification

> Tests covering Backend Matrix — Forced-Backend Probe.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Matrix Specification

## Scenarios

### Backend Matrix — Forced-Backend Probe

#### hardware backends

#### cuda probe — HARDWARE_PASS, UNAVAILABLE, or FAILED

- cuda probe — HARDWARE_PASS, UNAVAILABLE, or FAILED
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("cuda probe — HARDWARE_PASS, UNAVAILABLE, or FAILED")
val probe = probe_one("cuda")
val label = probe_result_label(probe)
print_probe(probe)
var ok = label == "HARDWARE_PASS" or label == "UNAVAILABLE" or label == "FAILED"
expect(ok).to_equal(true)
```

</details>

#### vulkan probe — HARDWARE_PASS, UNAVAILABLE, or FAILED

- vulkan probe — HARDWARE_PASS, UNAVAILABLE, or FAILED
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("vulkan probe — HARDWARE_PASS, UNAVAILABLE, or FAILED")
val probe = probe_one("vulkan")
val label = probe_result_label(probe)
print_probe(probe)
var ok = label == "HARDWARE_PASS" or label == "UNAVAILABLE" or label == "FAILED"
expect(ok).to_equal(true)
```

</details>

#### metal probe — HARDWARE_PASS, UNAVAILABLE, or FAILED

- metal probe — HARDWARE_PASS, UNAVAILABLE, or FAILED
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("metal probe — HARDWARE_PASS, UNAVAILABLE, or FAILED")
val probe = probe_one("metal")
val label = probe_result_label(probe)
print_probe(probe)
var ok = label == "HARDWARE_PASS" or label == "UNAVAILABLE" or label == "FAILED"
expect(ok).to_equal(true)
```

</details>

#### rocm probe — HARDWARE_PASS, UNAVAILABLE, or FAILED

- rocm probe — HARDWARE_PASS, UNAVAILABLE, or FAILED
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rocm probe — HARDWARE_PASS, UNAVAILABLE, or FAILED")
val probe = probe_one("rocm")
val label = probe_result_label(probe)
print_probe(probe)
var ok = label == "HARDWARE_PASS" or label == "UNAVAILABLE" or label == "FAILED"
expect(ok).to_equal(true)
```

</details>

#### intel probe — HARDWARE_PASS, UNAVAILABLE, or FAILED

- intel probe — HARDWARE_PASS, UNAVAILABLE, or FAILED
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("intel probe — HARDWARE_PASS, UNAVAILABLE, or FAILED")
val probe = probe_one("intel")
val label = probe_result_label(probe)
print_probe(probe)
var ok = label == "HARDWARE_PASS" or label == "UNAVAILABLE" or label == "FAILED"
expect(ok).to_equal(true)
```

</details>

#### qualcomm probe — HARDWARE_PASS, UNAVAILABLE, or FAILED

- qualcomm probe — HARDWARE_PASS, UNAVAILABLE, or FAILED
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("qualcomm probe — HARDWARE_PASS, UNAVAILABLE, or FAILED")
val probe = probe_one("qualcomm")
val label = probe_result_label(probe)
print_probe(probe)
var ok = label == "HARDWARE_PASS" or label == "UNAVAILABLE" or label == "FAILED"
expect(ok).to_equal(true)
```

</details>

#### webgpu probe — HARDWARE_PASS, UNAVAILABLE, or FAILED

- webgpu probe — HARDWARE_PASS, UNAVAILABLE, or FAILED
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("webgpu probe — HARDWARE_PASS, UNAVAILABLE, or FAILED")
val probe = probe_one("webgpu")
val label = probe_result_label(probe)
print_probe(probe)
var ok = label == "HARDWARE_PASS" or label == "UNAVAILABLE" or label == "FAILED"
expect(ok).to_equal(true)
```

</details>

#### opengl probe — HARDWARE_PASS, UNAVAILABLE, or FAILED

- opengl probe — HARDWARE_PASS, UNAVAILABLE, or FAILED
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("opengl probe — HARDWARE_PASS, UNAVAILABLE, or FAILED")
val probe = probe_one("opengl")
val label = probe_result_label(probe)
print_probe(probe)
var ok = label == "HARDWARE_PASS" or label == "UNAVAILABLE" or label == "FAILED"
expect(ok).to_equal(true)
```

</details>

#### software backends

#### software probe — SOFTWARE_PASS or FAILED

- software probe — SOFTWARE_PASS or FAILED
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("software probe — SOFTWARE_PASS or FAILED")
val probe = probe_one("software")
val label = probe_result_label(probe)
print_probe(probe)
var ok = label == "SOFTWARE_PASS" or label == "FAILED"
expect(ok).to_equal(true)
```

</details>

#### baseline cpu backend

#### cpu probe always passes

- cpu probe always passes
   - Expected: label equals `SOFTWARE_PASS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("cpu probe always passes")
val probe = probe_one("cpu")
val label = probe_result_label(probe)
print_probe(probe)
expect(label).to_equal("SOFTWARE_PASS")
```

</details>

#### cpu strict result is not Err

- cpu strict result is not Err
   - Expected: r.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("cpu strict result is not Err")
val r = Engine2D.create_with_backend_strict(16, 16, "cpu")
expect(r.is_ok()).to_equal(true)
if r.is_ok():
    var eng = r.unwrap()
    eng.shutdown()
```

</details>

#### no silent fallback

#### strict cuda never returns cpu on failure

- strict cuda never returns cpu on failure
   - Expected: is_fallback is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("strict cuda never returns cpu on failure")
val r = Engine2D.create_with_backend_strict(16, 16, "cuda")
if not r.is_ok():
    val probe = r.unwrap_err()
    val is_fallback = probe.is_ok() and probe.selected_name == "cpu"
    expect(is_fallback).to_equal(false)
```

</details>

#### strict vulkan never returns cpu on failure

- strict vulkan never returns cpu on failure
   - Expected: is_fallback is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("strict vulkan never returns cpu on failure")
val r = Engine2D.create_with_backend_strict(16, 16, "vulkan")
if not r.is_ok():
    val probe = r.unwrap_err()
    val is_fallback = probe.is_ok() and probe.selected_name == "cpu"
    expect(is_fallback).to_equal(false)
```

</details>

#### strict metal never returns cpu on failure

- strict metal never returns cpu on failure
   - Expected: is_fallback is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("strict metal never returns cpu on failure")
val r = Engine2D.create_with_backend_strict(16, 16, "metal")
if not r.is_ok():
    val probe = r.unwrap_err()
    val is_fallback = probe.is_ok() and probe.selected_name == "cpu"
    expect(is_fallback).to_equal(false)
```

</details>

#### strict webgpu never returns cpu on failure

- strict webgpu never returns cpu on failure
   - Expected: is_fallback is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("strict webgpu never returns cpu on failure")
val r = Engine2D.create_with_backend_strict(16, 16, "webgpu")
if not r.is_ok():
    val probe = r.unwrap_err()
    val is_fallback = probe.is_ok() and probe.selected_name == "cpu"
    expect(is_fallback).to_equal(false)
```

</details>

#### unknown backend returns Err not cpu

- unknown backend returns Err not cpu
   - Expected: r.is_ok() is false
   - Expected: probe.requested_name equals `does-not-exist`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("unknown backend returns Err not cpu")
val r = Engine2D.create_with_backend_strict(16, 16, "does-not-exist")
expect(r.is_ok()).to_equal(false)
val probe = r.unwrap_err()
print_probe(probe)
expect(probe.requested_name).to_equal("does-not-exist")
```

</details>

#### diagnostics

#### failed probe includes requested_name

- failed probe includes requested_name
   - Expected: probe.requested_name equals `cuda`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("failed probe includes requested_name")
val r = Engine2D.create_with_backend_strict(16, 16, "cuda")
if not r.is_ok():
    val probe = r.unwrap_err()
    expect(probe.requested_name).to_equal("cuda")
```

</details>

#### failed probe includes fallback_reason when unavailable

- failed probe includes fallback_reason when unavailable
   - Expected: reason_present is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("failed probe includes fallback_reason when unavailable")
val r = Engine2D.create_with_backend_strict(16, 16, "metal")
if not r.is_ok():
    val probe = r.unwrap_err()
    if probe.status == BackendStatus.Unavailable:
        var reason_present = probe.fallback_reason.len() > 0
        expect(reason_present).to_equal(true)
```

</details>

#### diagnostic_text contains requested and selected fields

- diagnostic_text contains requested and selected fields
   - Expected: has_requested is true
   - Expected: has_selected is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("diagnostic_text contains requested and selected fields")
val r = Engine2D.create_with_backend_strict(16, 16, "cuda")
if not r.is_ok():
    val probe = r.unwrap_err()
    val diag = probe.diagnostic_text()
    var has_requested = diag.contains("requested=cuda")
    var has_selected = diag.contains("selected=")
    expect(has_requested).to_equal(true)
    expect(has_selected).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/rendering/backend_matrix_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Backend Matrix — Forced-Backend Probe.
- Backend Matrix — Forced-Backend Probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `624bffc27b0fbb8fe8443bbaf2a0704b5be3c983e276142ea13289e95160cff5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `624bffc27b0fbb8fe8443bbaf2a0704b5be3c983e276142ea13289e95160cff5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `624bffc27b0fbb8fe8443bbaf2a0704b5be3c983e276142ea13289e95160cff5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/rendering/backend_matrix_spec.spl
mirror: doc/06_spec/integration/rendering/backend_matrix_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/rendering/backend_matrix_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/rendering/backend_matrix_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/rendering/backend_matrix_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cuda probe — HARDWARE_PASS, UNAVAILABLE, or FAILED' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/backend_matrix_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'vulkan probe — HARDWARE_PASS, UNAVAILABLE, or FAILED' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/backend_matrix_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'metal probe — HARDWARE_PASS, UNAVAILABLE, or FAILED' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
