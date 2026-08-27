# Backend Layer Artifact Evidence Specification

> Tests covering GPU backend layer artifact evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Layer Artifact Evidence Specification

## Scenarios

### GPU backend layer artifact evidence

#### keeps emission, validation, linking, and runtime admission separate

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps emission, validation, linking, and runtime admission separate
- emit artifact
   - Expected: file_exists(CHECK) is true
- validate artifact
   - Expected: code equals `0`
   - Expected: stderr equals ``
- link artifact
- run or read back


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps emission, validation, linking, and runtime admission separate")
step("emit artifact")
expect(file_exists(CHECK)).to_equal(true)
val checker = file_read(CHECK)
expect(checker).to_contain("layer_result \"$backend\" emit")
expect(checker).to_contain("producer-exit-")

step("validate artifact")
val (stdout, stderr, code) = process_run("/bin/sh", [CHECK, "--self-test"])
expect(code).to_equal(0)
expect(stderr).to_equal("")
expect(stdout).to_contain("gpu_backend_layer_self_test=PASS")
expect(stdout).to_contain("cuda_validate_result=PASS")
expect(stdout).to_contain("cuda_validate_result=SKIP_UNAVAILABLE")
expect(stdout).to_contain("cuda_validate_result=FAIL")
expect(stdout).to_contain("cuda_validate_reason=verified-status-without-artifact")
expect(stdout).to_contain("cuda_validate_reason=missing-validator-tool")
expect(stdout).to_contain("cuda_validate_reason=source-emission-failed")
expect(stdout).to_contain("cuda_validate_reason=unknown-artifact-status")

step("link artifact")
expect(stdout).to_contain("cuda_link_result=PASS")
expect(stdout).to_contain("cuda_link_result=SKIP_UNAVAILABLE")
expect(stdout).to_contain("cuda_link_result=FAIL")

step("run or read back")
expect(stdout).to_contain("cuda_runtime_result=PASS")
expect(stdout).to_contain("cuda_runtime_result=SKIP_UNAVAILABLE")
expect(stdout).to_contain("cuda_runtime_reason=zero-exit-without-pass-receipt")
expect(stdout).to_contain("cuda_runtime_reason=runtime-check-failed")
```

</details>

#### rejects unknown command-line arguments with usage status

- rejects unknown command-line arguments with usage status
   - Expected: code equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects unknown command-line arguments with usage status")
val (_stdout, stderr, code) = process_run("/bin/sh", [CHECK, "--unknown-option"])
expect(code).to_equal(64)
expect(stderr).to_contain("unknown argument: --unknown-option")
```

</details>

#### identifies Metal, HIP, and OpenCL without inventing a Metal BackendKind

- identifies Metal, HIP, and OpenCL without inventing a Metal BackendKind
   - Expected: code equals `0`
   - Expected: stdout does not contain `metal_backend_kind=true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("identifies Metal, HIP, and OpenCL without inventing a Metal BackendKind")
val (stdout, _stderr, code) = process_run("/bin/sh", [CHECK, "--self-test"])
expect(code).to_equal(0)
expect(stdout).to_contain("metal_layer=portable_compute_renderer")
expect(stdout).to_contain("metal_backend_kind=false")
expect(stdout).to_contain("hip_backend_kind_status=unimplemented")
expect(stdout).to_contain("opencl_backend_kind_status=implemented")
expect(stdout.contains("metal_backend_kind=true")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | GPU & SIMD |
| Status | Active |
| Source | `test/03_system/gpu/backend_layer_artifact_evidence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering GPU backend layer artifact evidence.
- GPU backend layer artifact evidence

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9bc847235d29cb35796b94de6777d3efe3beea06a6a5bac252005945d8ceadfe`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9bc847235d29cb35796b94de6777d3efe3beea06a6a5bac252005945d8ceadfe`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9bc847235d29cb35796b94de6777d3efe3beea06a6a5bac252005945d8ceadfe`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/gpu/backend_layer_artifact_evidence_spec.spl
mirror: doc/06_spec/03_system/gpu/backend_layer_artifact_evidence_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gpu/backend_layer_artifact_evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gpu/backend_layer_artifact_evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gpu/backend_layer_artifact_evidence_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gpu/backend_layer_artifact_evidence_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps emission, validation, linking, and runtime admission separate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gpu/backend_layer_artifact_evidence_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unknown command-line arguments with usage status' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gpu/backend_layer_artifact_evidence_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identifies Metal, HIP, and OpenCL without inventing a Metal BackendKind' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
