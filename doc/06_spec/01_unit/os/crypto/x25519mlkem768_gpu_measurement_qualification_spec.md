# x25519mlkem768_gpu_measurement_qualification_spec

> Verifies the x25519mlkem768 gpu measurement qualification behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# x25519mlkem768_gpu_measurement_qualification_spec

Verifies the x25519mlkem768 gpu measurement qualification behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_gpu_measurement_qualification_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the x25519mlkem768 gpu measurement qualification behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### X25519MLKEM768 fail-closed GPU measurement qualification

#### admits exact CUDA and Vulkan rows and keeps Metal blocked

- Verify: admits exact CUDA and Vulkan rows and keeps Metal blocked
- Bind qualification execution lifecycle and canonical build tuple


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-007 REQ-010 REQ-011 REQ-012
step("Verify: admits exact CUDA and Vulkan rows and keeps Metal blocked")
step("Bind qualification execution lifecycle and canonical build tuple")
for backend in [X25519MlKem768EvidenceBackend.Cuda,
        X25519MlKem768EvidenceBackend.Vulkan]:
    val qualification = _gpu_qualification(backend)
    expect(_gpu_reason(
        qualification, _gpu_config(qualification),
        _gpu_evidence(qualification), _gpu_delta())).to_equal("")
val metal = _gpu_qualification(X25519MlKem768EvidenceBackend.Metal)
expect(_gpu_reason(metal, _gpu_config(metal),
    _gpu_evidence(metal), _gpu_delta())).to_equal(
    "gpu-build-metal-metallib-and-live-identity-not-pinned")
```

</details>

#### rejects invalid qualification policy version and batch first

- Verify: rejects invalid qualification policy version and batch first


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-007 REQ-010 REQ-011 REQ-012
step("Verify: rejects invalid qualification policy version and batch first")
val qualification = _gpu_qualification(
    X25519MlKem768EvidenceBackend.Cuda)
val evidence = _gpu_evidence(qualification)
var invalid = qualification
invalid.qualification_sha256 = "0" * 64
expect(_gpu_reason(
    invalid, _gpu_config(qualification), evidence,
    _gpu_delta())).to_equal("gpu-measurement-qualification-invalid")

var suggest = _gpu_config(qualification)
suggest.selection_mode = X25519MlKem768SelectionMode.Suggest
expect(_gpu_reason(
    qualification, suggest, evidence, _gpu_delta())).to_equal(
    "gpu-measurement-config-policy-mismatch")

var wrong_version = _gpu_config(qualification)
wrong_version.profile_version = "wrong"
expect(_gpu_reason(
    qualification, wrong_version, evidence, _gpu_delta())).to_equal(
    "gpu-measurement-config-version-mismatch")

var bad_batch = _gpu_config(qualification)
bad_batch.minimum_batch = bad_batch.batch_size + 1
expect(_gpu_reason(
    qualification, bad_batch, evidence, _gpu_delta())).to_equal(
    "gpu-measurement-config-batch-mismatch")
```

</details>

#### rejects execution substitution fallback and lifecycle gaps

- Verify: rejects execution substitution fallback and lifecycle gaps


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-007 REQ-010 REQ-011 REQ-012
step("Verify: rejects execution substitution fallback and lifecycle gaps")
val qualification = _gpu_qualification(
    X25519MlKem768EvidenceBackend.Cuda)
val config = _gpu_config(qualification)
val evidence = _gpu_evidence(qualification)

var wrong_backend = evidence
wrong_backend.selected_backend = X25519MlKem768Backend.Vulkan
expect(_gpu_reason(
    qualification, config, wrong_backend, _gpu_delta())).to_equal(
    "gpu-measurement-executed-backend-mismatch")

var wrong_artifact = evidence
wrong_artifact.artifact_digest = "8" * 64
expect(_gpu_reason(
    qualification, config, wrong_artifact, _gpu_delta())).to_equal(
    "gpu-measurement-execution-binding-mismatch")

var wrong_device = evidence
wrong_device.executor_identity = "cuda-device:99"
expect(_gpu_reason(
    qualification, config, wrong_device, _gpu_delta())).to_equal(
    "gpu-measurement-device-identity-mismatch")

var fallback = evidence
fallback.fallback_used = true
expect(_gpu_reason(
    qualification, config, fallback, _gpu_delta())).to_equal(
    "gpu-measurement-fallback-or-oracle-mismatch")

var incomplete = evidence
incomplete.device_readback = false
expect(_gpu_reason(
    qualification, config, incomplete, _gpu_delta())).to_equal(
    "gpu-measurement-device-lifecycle-incomplete")

var invalid_delta = _gpu_delta()
invalid_delta.readback_count = 2
expect(_gpu_reason(
    qualification, config, evidence, invalid_delta)).to_equal(
    "gpu-measurement-lifecycle-delta-invalid")

var wrong_count = evidence
wrong_count.kernel_invocations = 4
expect(_gpu_reason(
    qualification, config, wrong_count, _gpu_delta())).to_equal(
    "gpu-measurement-kernel-count-mismatch")
```

</details>

#### rejects forged cross-runner and cross-device build admissions

- Verify: rejects forged cross-runner and cross-device build admissions


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-007 REQ-010 REQ-011 REQ-012
step("Verify: rejects forged cross-runner and cross-device build admissions")
val qualification = _gpu_qualification(
    X25519MlKem768EvidenceBackend.Cuda)
val config = _gpu_config(qualification)
val evidence = _gpu_evidence(qualification)
var runner = _gpu_admission_for(qualification)
runner.runner_artifact_sha256 = "2" * 64
expect(x25519_mlkem768_qualified_gpu_measurement_reason(
    qualification, config, runner, evidence, _gpu_delta())).to_equal(
    "gpu-build-qualification-runner-artifact-mismatch")
var device = _gpu_admission_for(qualification)
device.live_device_identity_tag = 99
device.live_device_identity = "cuda-device-identity:99"
expect(x25519_mlkem768_qualified_gpu_measurement_reason(
    qualification, config, device, evidence, _gpu_delta())).to_equal(
    "gpu-build-qualification-stable-executor-identity-mismatch")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ea4e8b562103757f5e6702ba0fb8823b9694e00afdf84f0ab0cdae84ed13d8dd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ea4e8b562103757f5e6702ba0fb8823b9694e00afdf84f0ab0cdae84ed13d8dd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ea4e8b562103757f5e6702ba0fb8823b9694e00afdf84f0ab0cdae84ed13d8dd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/crypto/x25519mlkem768_gpu_measurement_qualification_spec.spl
mirror: doc/06_spec/01_unit/os/crypto/x25519mlkem768_gpu_measurement_qualification_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/crypto/x25519mlkem768_gpu_measurement_qualification_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/crypto/x25519mlkem768_gpu_measurement_qualification_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/crypto/x25519mlkem768_gpu_measurement_qualification_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
