# Backend Session Contract Specification

> Tests covering Engine2D backend session compute contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Session Contract Specification

## Scenarios

### Engine2D backend session compute contract

#### exposes compute backend kinds for the shared session plan

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exposes compute backend kinds for the shared session plan
   - Expected: ComputeSessionKind.cpu_simd().kind equals `cpu_simd`
   - Expected: ComputeSessionKind.hip().kind equals `hip`
   - Expected: ComputeSessionKind.rocm().kind equals `rocm`
   - Expected: ComputeSessionKind.opencl().kind equals `opencl`
   - Expected: ComputeSessionKind.qualcomm().kind equals `qualcomm`
   - Expected: compute_session_kind_name(ComputeSessionKind.opencl()) equals `opencl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("exposes compute backend kinds for the shared session plan")
expect(ComputeSessionKind.cpu_simd().kind).to_equal("cpu_simd")
expect(ComputeSessionKind.hip().kind).to_equal("hip")
expect(ComputeSessionKind.rocm().kind).to_equal("rocm")
expect(ComputeSessionKind.opencl().kind).to_equal("opencl")
expect(ComputeSessionKind.qualcomm().kind).to_equal("qualcomm")
expect(compute_session_kind_name(ComputeSessionKind.opencl())).to_equal("opencl")
```

</details>

#### maps public backend names to session kinds

- maps public backend names to session kinds
   - Expected: resolved_kind_name("cpu_simd") equals `cpu_simd`
   - Expected: resolved_kind_name("hip") equals `hip`
   - Expected: resolved_kind_name("rocm") equals `rocm`
   - Expected: resolved_kind_name("opencl") equals `opencl`
   - Expected: resolved_kind_name("qualcomm") equals `qualcomm`
   - Expected: resolved_kind_name("cuda") equals `cuda`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps public backend names to session kinds")
expect(resolved_kind_name("cpu_simd")).to_equal("cpu_simd")
expect(resolved_kind_name("hip")).to_equal("hip")
expect(resolved_kind_name("rocm")).to_equal("rocm")
expect(resolved_kind_name("opencl")).to_equal("opencl")
expect(resolved_kind_name("qualcomm")).to_equal("qualcomm")
expect(resolved_kind_name("cuda")).to_equal("cuda")
```

</details>

#### carries portable compute errors for unavailable backends

- carries portable compute errors for unavailable backends
   - Expected: err.kind equals `opencl`
   - Expected: err.code equals `1`
   - Expected: err.message equals `missing OpenCL ICD`
   - Expected: err.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("carries portable compute errors for unavailable backends")
val err = compute_session_error_unavailable(ComputeSessionKind.opencl(), "missing OpenCL ICD")

expect(err.kind).to_equal("opencl")
expect(err.code).to_equal(1)
expect(err.message).to_equal("missing OpenCL ICD")
expect(err.is_ok()).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/backend_session_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine2D backend session compute contract.
- Engine2D backend session compute contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0f51ef24ed7654bd3979c4d56d74b34f8a6d45a2bc6f6a56306774b79fe64660`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0f51ef24ed7654bd3979c4d56d74b34f8a6d45a2bc6f6a56306774b79fe64660`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0f51ef24ed7654bd3979c4d56d74b34f8a6d45a2bc6f6a56306774b79fe64660`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/gpu/engine2d/backend_session_contract_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine2d/backend_session_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/engine2d/backend_session_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine2d/backend_session_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/engine2d/backend_session_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gpu/engine2d/backend_session_contract_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes compute backend kinds for the shared session plan' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/backend_session_contract_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps public backend names to session kinds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/backend_session_contract_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'carries portable compute errors for unavailable backends' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
