# X25519mlkem768 Cuda Binary Execution Specification

> Tests covering X25519MLKEM768 pure-Simple exact CUDA binary execution.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Cuda Binary Execution Specification

## Scenarios

### X25519MLKEM768 pure-Simple exact CUDA binary execution

#### should load admitted sm86 cubin bytes and execute both NTT entries

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should load admitted sm86 cubin bytes and execute both NTT entries
- Verify cubin provenance and execute forward and inverse NTT
   - Expected: retained_digest equals `_SM86_CUBIN_SHA256`
   - Expected: admitted_byte_count equals `retained_byte_count`
   - Expected: admitted_digest equals `_SM86_CUBIN_SHA256`
   - Expected: source_digest equals ``
   - Expected: forward.kernel_invocations equals `1`
   - Expected: forward.artifact_digest equals `_SM86_CUBIN_SHA256`
   - Expected: inverse.device_identity equals `forward.device_identity`
   - Expected: inverse.kernel_invocations equals `1`
   - Expected: inverse.artifact_digest equals `_SM86_CUBIN_SHA256`
   - Expected: generation equals `1`
   - Expected: invocation_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 62 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should load admitted sm86 cubin bytes and execute both NTT entries")
step("Verify cubin provenance and execute forward and inverse NTT")
val host_available = cuda_available()
expect(host_available).to_be(true)

val retained_digest = file_hash_sha256(_SM86_CUBIN_PATH)
val retained_byte_count = file_size(_SM86_CUBIN_PATH)
expect(retained_digest).to_equal(_SM86_CUBIN_SHA256)
expect(retained_byte_count).to_be_greater_than(0)

val fixture = x25519_mlkem768_ntt_fixture(1)
val expected_forward = ntt(fixture)
val expected_inverse = intt(expected_forward)
var executor = X25519MlKem768CudaNttExecutor.create_binary(
    _SM86_CUBIN_PATH, _SM86_CUBIN_SHA256)
val admitted_byte_count = executor.artifact_bytes.len()
val independently_hashed_admitted_bytes =
    sha256_u8_hex(executor.artifact_bytes)
val admitted_digest = executor.artifact_digest
val binary_mode = executor.use_binary
val source_digest = executor.source_digest
expect(admitted_byte_count).to_equal(retained_byte_count)
expect(independently_hashed_admitted_bytes).to_equal(
    _SM86_CUBIN_SHA256)
expect(admitted_digest).to_equal(_SM86_CUBIN_SHA256)
expect(binary_mode).to_be(true)
expect(source_digest).to_equal("")

val forward = x25519_mlkem768_cuda_ntt_execute(executor, fixture)
expect(forward.completed).to_be(true)
expect(forward.compiled).to_be(true)
expect(forward.submitted).to_be(true)
expect(forward.fence_completed).to_be(true)
expect(forward.device_readback).to_be(true)
expect(forward.device_identity).to_be_greater_than(0)
expect(forward.kernel_invocations).to_equal(1)
expect(forward.artifact_digest).to_equal(_SM86_CUBIN_SHA256)
expect(_cuda_binary_lists_equal(
    forward.values, expected_forward)).to_be(true)

val inverse = x25519_mlkem768_cuda_intt_execute(
    executor, forward.values)
expect(inverse.completed).to_be(true)
expect(inverse.compiled).to_be(true)
expect(inverse.submitted).to_be(true)
expect(inverse.fence_completed).to_be(true)
expect(inverse.device_readback).to_be(true)
expect(inverse.device_identity).to_equal(forward.device_identity)
expect(inverse.kernel_invocations).to_equal(1)
expect(inverse.artifact_digest).to_equal(_SM86_CUBIN_SHA256)
expect(_cuda_binary_lists_equal(
    inverse.values, expected_inverse)).to_be(true)

val module_loaded = executor.session.module > 0
val generation = executor.session.generation
val invocation_count = executor.kernel_invocations
executor.shutdown()

expect(module_loaded).to_be(true)
expect(generation).to_equal(1)
expect(invocation_count).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/crypto/x25519mlkem768_cuda_binary_execution_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 pure-Simple exact CUDA binary execution.
- X25519MLKEM768 pure-Simple exact CUDA binary execution

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bfb34ebe17a1ee67d9db4d048811f01bde2f6ae87a8e994fce512832a862b693`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bfb34ebe17a1ee67d9db4d048811f01bde2f6ae87a8e994fce512832a862b693`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bfb34ebe17a1ee67d9db4d048811f01bde2f6ae87a8e994fce512832a862b693`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/02_integration/os/crypto/x25519mlkem768_cuda_binary_execution_spec.spl
mirror: doc/06_spec/02_integration/os/crypto/x25519mlkem768_cuda_binary_execution_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=95 oracle=20
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/02_integration/os/crypto/x25519mlkem768_cuda_binary_execution_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/os/crypto/x25519mlkem768_cuda_binary_execution_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/os/crypto/x25519mlkem768_cuda_binary_execution_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario compares only locally constructed arithmetic or literals
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/02_integration/os/crypto/x25519mlkem768_cuda_binary_execution_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/os/crypto/x25519mlkem768_cuda_binary_execution_spec.spl:39:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should load admitted sm86 cubin bytes and execute both NTT entries' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/os/crypto/x25519mlkem768_cuda_binary_execution_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should load admitted sm86 cubin bytes and execute both NTT entries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
