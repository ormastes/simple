# X25519mlkem768 Cuda Warmup Contract Specification

> Tests covering X25519MLKEM768 CUDA cold setup contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Cuda Warmup Contract Specification

## Scenarios

### X25519MLKEM768 CUDA cold setup contract

#### should fail closed on missing pinned PTX before CUDA access for NFR-012

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should fail closed on missing pinned PTX before CUDA access for NFR-012
- Warm a CUDA executor whose pinned PTX artifact is missing
   - Expected: executor.warmup() equals `cuda-ntt-artifact-invalid`
   - Expected: executor.warmup() equals `cuda-ntt-artifact-invalid`
   - Expected: executor.kernel_invocations equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should fail closed on missing pinned PTX before CUDA access for NFR-012")
step("Warm a CUDA executor whose pinned PTX artifact is missing")
var executor = X25519MlKem768CudaNttExecutor.create(
    "test/fixtures/crypto/x25519mlkem768/missing.ptx")
expect(executor.warmup()).to_equal("cuda-ntt-artifact-invalid")
expect(executor.warmup()).to_equal("cuda-ntt-artifact-invalid")
expect(executor.kernel_invocations).to_equal(0)
executor.shutdown()
```

</details>

#### should fail closed on missing pinned CUBIN before CUDA access for NFR-012

- should fail closed on missing pinned CUBIN before CUDA access for NFR-012
- Warm a CUDA executor whose pinned CUBIN artifact is missing
   - Expected: executor.kernel_invocations equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should fail closed on missing pinned CUBIN before CUDA access for NFR-012")
step("Warm a CUDA executor whose pinned CUBIN artifact is missing")
var executor = X25519MlKem768CudaNttExecutor.create_binary(
    "test/fixtures/crypto/x25519mlkem768/missing.cubin",
    "0000000000000000000000000000000000000000000000000000000000000000")
expect(executor.warmup()).to_equal(
    "cuda-ntt-binary-artifact-invalid")
expect(executor.warmup()).to_equal(
    "cuda-ntt-binary-artifact-invalid")
expect(executor.kernel_invocations).to_equal(0)
executor.shutdown()
```

</details>

#### should validate provenance before initialization and load once for NFR-012

- should validate provenance before initialization and load once for NFR-012
- Inspect CUDA warmup ordering, module reuse, and process isolation


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should validate provenance before initialization and load once for NFR-012")
step("Inspect CUDA warmup ordering, module reuse, and process isolation")
val provider = file_read_text(
    "src/os/crypto/x25519_mlkem768/cuda_ntt_provider.spl")
val warmup = provider.index_of("me warmup() -> text:")
val warmup_ready = provider.index_of("self._ensure_ready()", warmup)
val ensure_ready = provider.index_of("me _ensure_ready() -> text:")
val binary_digest = provider.index_of(
    "self.artifact_digest != self.expected_artifact_digest",
    ensure_ready)
val source_digest = provider.index_of(
    "self.source_digest != self.expected_source_digest",
    ensure_ready)
val initialize = provider.index_of("self.session.init()", ensure_ready)
val module_guard = provider.index_of(
    "if self.session.module == 0:", ensure_ready)
val module_load = provider.index_of(
    "self.session.load_module(", module_guard)
val device_identity = provider.index_of(
    "val identity = self.session.identity()", module_guard)
val cache_device_bind = provider.index_of(
    "x25519_mlkem768_cache_bind_device(", device_identity)
val execute = provider.index_of("fn _cuda_ntt_execute(")
val launch = provider.index_of("executor.session.launch(", execute)
expect(warmup).to_be_greater_than(0)
expect(warmup_ready).to_be_greater_than(warmup)
expect(binary_digest).to_be_less_than(initialize)
expect(source_digest).to_be_less_than(initialize)
expect(module_guard).to_be_greater_than(initialize)
expect(module_load).to_be_greater_than(module_guard)
expect(device_identity).to_be_greater_than(module_load)
expect(cache_device_bind).to_be_greater_than(device_identity)
expect(launch).to_be_greater_than(execute)
expect(warmup).to_be_less_than(execute)
expect(provider.contains("process_run(")).to_be(false)
expect(provider.contains("rt_process_run")).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_cuda_warmup_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 CUDA cold setup contract.
- X25519MLKEM768 CUDA cold setup contract

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cbbb1c9ebbfa95c6a117e61ed4b6ffbaf37c6a086fa0d902cffdd5920f954eb8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cbbb1c9ebbfa95c6a117e61ed4b6ffbaf37c6a086fa0d902cffdd5920f954eb8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cbbb1c9ebbfa95c6a117e61ed4b6ffbaf37c6a086fa0d902cffdd5920f954eb8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/crypto/x25519mlkem768_cuda_warmup_contract_spec.spl
mirror: doc/06_spec/01_unit/os/crypto/x25519mlkem768_cuda_warmup_contract_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/crypto/x25519mlkem768_cuda_warmup_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/crypto/x25519mlkem768_cuda_warmup_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/crypto/x25519mlkem768_cuda_warmup_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/crypto/x25519mlkem768_cuda_warmup_contract_spec.spl:20:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fail closed on missing pinned PTX before CUDA access for NFR-012' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_cuda_warmup_contract_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should fail closed on missing pinned PTX before CUDA access for NFR-012' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_cuda_warmup_contract_spec.spl:31:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fail closed on missing pinned CUBIN before CUDA access for NFR-012' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_cuda_warmup_contract_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should fail closed on missing pinned CUBIN before CUDA access for NFR-012' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_cuda_warmup_contract_spec.spl:45:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should validate provenance before initialization and load once for NFR-012' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_cuda_warmup_contract_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should validate provenance before initialization and load once for NFR-012' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
