# @manual: primary

> Purpose: Prove that X25519MLKEM768 extracted operation evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that X25519MLKEM768 extracted operation evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_operation_evidence_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that X25519MLKEM768 extracted operation evidence.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
# @manual: primary
REQ-OS-CRYPTO-001
doc/01_research/local/REQ-OS-CRYPTO-001.md
doc/03_plan/sys_test/REQ-OS-CRYPTO-001.md
doc/04_architecture/REQ-OS-CRYPTO-001.md
doc/05_design/REQ-OS-CRYPTO-001.md

## Scenarios

### X25519MLKEM768 extracted operation evidence

#### should keep every extracted module below 800 lines

- Count the GPU, SIMD, and hybrid module lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-CRYPTO-001
step("Count the GPU, SIMD, and hybrid module lines")
val gpu = file_read_text(
    "src/os/crypto/x25519_mlkem768/gpu_operation_evidence.spl")
val simd = file_read_text(
    "src/os/crypto/x25519_mlkem768/simd_operation_evidence.spl")
val hybrid = file_read_text(
    "src/os/crypto/x25519_mlkem768/hybrid.spl")
expect(gpu.split("\n").len()).to_be_less_than(800)
expect(simd.split("\n").len()).to_be_less_than(800)
expect(hybrid.split("\n").len()).to_be_less_than(800)
```

</details>

#### should map all three GPU providers through all three scalar checks

- Count keygen, encapsulation, and decapsulation verifier calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-CRYPTO-001
step("Count keygen, encapsulation, and decapsulation verifier calls")
val gpu = file_read_text(
    "src/os/crypto/x25519_mlkem768/gpu_operation_evidence.spl")
val hybrid = file_read_text(
    "src/os/crypto/x25519_mlkem768/hybrid.spl")
val implementation = gpu + hybrid
expect(implementation.split(
    "x25519_mlkem768_verify_gpu_keygen(").len()).to_equal(5)
expect(implementation.split(
    "x25519_mlkem768_verify_gpu_encapsulate(").len()).to_equal(5)
expect(implementation.split(
    "x25519_mlkem768_verify_gpu_decapsulate(").len()).to_equal(5)
```

</details>

#### should compare paired secret-bearing results before branching

- Inspect constant-work scalar differential comparisons


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-CRYPTO-001
step("Inspect constant-work scalar differential comparisons")
val gpu = file_read_text(
    "src/os/crypto/x25519_mlkem768/gpu_operation_evidence.spl")
expect(gpu).to_contain("val encapsulation_key_matches =")
expect(gpu).to_contain("val decapsulation_key_matches =")
expect(gpu).to_contain("val shared_matches =")
expect(gpu).to_contain("val ciphertext_matches =")
expect(gpu).to_contain(
    "var difference: i64 = left.len() ^ right.len()")
expect(gpu.contains(
    "if left.len() != right.len()")).to_equal(false)
expect(gpu.contains(
    "if (not _gpu_lists_equal(encapsulation_key")).to_equal(false)
expect(gpu.contains(
    "if (not _gpu_lists_equal(mlkem_shared")).to_equal(false)
```

</details>

#### should fail closed without a current GPU lifecycle receipt

- Inspect invocation and readback gates before evidence promotion
   - Expected: gpu.split("operation_invocations < 1").len() equals `4`
   - Expected: gpu.split(baseline_guard).len() equals `4`
   - Expected: gpu.split("if not executor.fence_completed").len() equals `4`
   - Expected: gpu.split("updated.device_readback = true").len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-CRYPTO-001
step("Inspect invocation and readback gates before evidence promotion")
val gpu = file_read_text(
    "src/os/crypto/x25519_mlkem768/gpu_operation_evidence.spl")
val hybrid = file_read_text(
    "src/os/crypto/x25519_mlkem768/hybrid.spl")
expect(gpu.split("operation_invocations < 1").len()).to_equal(4)
val baseline_guard =
    "invocations_before < 0 or executor.kernel_invocations < invocations_before"
expect(gpu.split(baseline_guard).len()).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(gpu.split("if not executor.fence_completed").len()).to_equal(4)
expect(gpu.split("updated.device_readback = true").len()).to_equal(4)
expect(hybrid.split(
    "match x25519_mlkem768_cuda_operation_evidence(").len()).to_equal(4)
expect(hybrid.split(
    "match x25519_mlkem768_metal_operation_evidence(").len()).to_equal(4)
expect(hybrid.split(
    "match x25519_mlkem768_vulkan_operation_evidence(").len()).to_equal(4)
```

</details>

#### should bind Metal receipts to the stable registry identity

- Reject display-name identity substitution before receipt promotion


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-CRYPTO-001
step("Reject display-name identity substitution before receipt promotion")
val gpu = file_read_text(
    "src/os/crypto/x25519_mlkem768/gpu_operation_evidence.spl")
expect(gpu).to_contain("val stable_device_identity = " +
    "executor.session.stable_device_identity")
expect(gpu).to_contain(
    "Metal full operation stable device identity unavailable")
expect(gpu).to_contain(
    "\"metal-device:\" + stable_device_identity")
expect(gpu.contains(
    "\"metal-device:\" + executor.session.device_name")).to_equal(false)
```

</details>

#### should retain admitted SIMD artifact provenance as execution proof

- Separate runtime provenance proof from the public output digest
   - Expected: scalar_proof_count equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-CRYPTO-001
step("Separate runtime provenance proof from the public output digest")
val simd = file_read_text(
    "src/os/crypto/x25519_mlkem768/simd_operation_evidence.spl")
val hybrid = file_read_text(
    "src/os/crypto/x25519_mlkem768/hybrid.spl")
expect(simd).to_contain(
    "updated.execution_proof_digest = updated.artifact_digest")
# Only the three scalar operations use their public output as proof.
val scalar_proof_count = hybrid.split(
    "evidence.execution_proof_digest = evidence.output_digest").len()
expect(scalar_proof_count).to_equal(4)  # oracle: 4 — named expected value from the requirement
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

- `REQ-OS-CRYPTO-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5747ed44818c3d5fb72f60489301512fd19ba7182267f3955839b06ff3702a64`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5747ed44818c3d5fb72f60489301512fd19ba7182267f3955839b06ff3702a64`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5747ed44818c3d5fb72f60489301512fd19ba7182267f3955839b06ff3702a64`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/01_unit/os/crypto/x25519mlkem768_operation_evidence_contract_spec.spl
mirror: doc/06_spec/01_unit/os/crypto/x25519mlkem768_operation_evidence_contract_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/crypto/x25519mlkem768_operation_evidence_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/crypto/x25519mlkem768_operation_evidence_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/crypto/x25519mlkem768_operation_evidence_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/crypto/x25519mlkem768_operation_evidence_contract_spec.spl:33:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep every extracted module below 800 lines' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_operation_evidence_contract_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep every extracted module below 800 lines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_operation_evidence_contract_spec.spl:46:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should map all three GPU providers through all three scalar checks' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_operation_evidence_contract_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should map all three GPU providers through all three scalar checks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_operation_evidence_contract_spec.spl:61:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should compare paired secret-bearing results before branching' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_operation_evidence_contract_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should compare paired secret-bearing results before branching' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_operation_evidence_contract_spec.spl:79:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fail closed without a current GPU lifecycle receipt' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_operation_evidence_contract_spec.spl:99:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bind Metal receipts to the stable registry identity' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_operation_evidence_contract_spec.spl:113:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain admitted SIMD artifact provenance as execution proof' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
