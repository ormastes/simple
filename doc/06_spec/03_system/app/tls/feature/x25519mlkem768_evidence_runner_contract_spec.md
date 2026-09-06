# x25519mlkem768_evidence_runner_contract_spec

> Behavioral fail-closed contract for X25519MLKEM768 GPU evidence dispatch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# x25519mlkem768_evidence_runner_contract_spec

Behavioral fail-closed contract for X25519MLKEM768 GPU evidence dispatch.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/tls/feature/x25519mlkem768_evidence_runner_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Behavioral fail-closed contract for X25519MLKEM768 GPU evidence dispatch.

These scenarios call the public dispatch boundary. They do not inspect source
text and cannot turn an unavailable GPU backend into passing evidence.

## Scenarios

### X25519MLKEM768 GPU evidence dispatch

#### should reject a manifest identity mismatch before artifact admission

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should reject a manifest identity mismatch before artifact admission
- Dispatch a CUDA request whose manifest digest is mismatched


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject a manifest identity mismatch before artifact admission")
step("Dispatch a CUDA request whose manifest digest is mismatched")
var request = _request(X25519MlKem768EvidenceBackend.Cuda)
request.fixture_manifest_sha256 = "0" * 64
val result = x25519_mlkem768_dispatch_gpu(request)
_expect_blocked(
    result, "gpu-fixture-manifest-content-sha256-mismatch")
```

</details>

#### should reject missing exact-binary admission artifacts

- should reject missing exact-binary admission artifacts
- Dispatch a CUDA request without a compiler artifact


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing exact-binary admission artifacts")
step("Dispatch a CUDA request without a compiler artifact")
val result = x25519_mlkem768_dispatch_gpu(
    _request(X25519MlKem768EvidenceBackend.Cuda))
_expect_blocked(result, "missing-compiler-artifact")
```

</details>

#### should reject auxiliary artifacts on a CUDA row

- should reject auxiliary artifacts on a CUDA row
- Dispatch a CUDA request with an impossible auxiliary tuple


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject auxiliary artifacts on a CUDA row")
step("Dispatch a CUDA request with an impossible auxiliary tuple")
var request = _request(X25519MlKem768EvidenceBackend.Cuda)
request.compiler_artifact = "compiler"
request.compiler_provenance = "compiler.provenance.env"
request.runner_artifact = "runner"
request.accelerator_binding = "binding"
request.accelerator_source = "source"
request.accelerator_binary = "binary"
request.accelerator_source_aux = "unexpected-source"
val result = x25519_mlkem768_dispatch_gpu(request)
_expect_blocked(result, "unexpected-auxiliary-accelerator-artifact")
```

</details>

#### should require exact Vulkan artifacts before capability admission

- should require exact Vulkan artifacts before capability admission
- Dispatch a Vulkan row without its exact compiler artifact


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require exact Vulkan artifacts before capability admission")
step("Dispatch a Vulkan row without its exact compiler artifact")
val result = x25519_mlkem768_dispatch_gpu(
    _request(X25519MlKem768EvidenceBackend.Vulkan))
_expect_blocked(result, "missing-compiler-artifact")
```

</details>

#### should keep Metal unavailable without an unpinned binary

- should keep Metal unavailable without an unpinned binary
- Dispatch an unavailable Metal row


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep Metal unavailable without an unpinned binary")
step("Dispatch an unavailable Metal row")
val result = x25519_mlkem768_dispatch_gpu(
    _request(X25519MlKem768EvidenceBackend.Metal))
_expect_blocked(
    result, "metal-binary-digest-not-pinned-by-fixture-manifest")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `51f3ef2a1438bc247c894584b426918a0a3e65c149bf1ac6473d062f20065e2c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `51f3ef2a1438bc247c894584b426918a0a3e65c149bf1ac6473d062f20065e2c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `51f3ef2a1438bc247c894584b426918a0a3e65c149bf1ac6473d062f20065e2c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/app/tls/feature/x25519mlkem768_evidence_runner_contract_spec.spl
mirror: doc/06_spec/03_system/app/tls/feature/x25519mlkem768_evidence_runner_contract_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=75 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/tls/feature/x25519mlkem768_evidence_runner_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/tls/feature/x25519mlkem768_evidence_runner_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/tls/feature/x25519mlkem768_evidence_runner_contract_spec.spl:64:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject a manifest identity mismatch before artifact admission' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/tls/feature/x25519mlkem768_evidence_runner_contract_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject a manifest identity mismatch before artifact admission' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/tls/feature/x25519mlkem768_evidence_runner_contract_spec.spl:74:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject missing exact-binary admission artifacts' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/tls/feature/x25519mlkem768_evidence_runner_contract_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject missing exact-binary admission artifacts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/tls/feature/x25519mlkem768_evidence_runner_contract_spec.spl:82:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject auxiliary artifacts on a CUDA row' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/tls/feature/x25519mlkem768_evidence_runner_contract_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject auxiliary artifacts on a CUDA row' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/tls/feature/x25519mlkem768_evidence_runner_contract_spec.spl:97:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require exact Vulkan artifacts before capability admission' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/tls/feature/x25519mlkem768_evidence_runner_contract_spec.spl:105:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep Metal unavailable without an unpinned binary' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
