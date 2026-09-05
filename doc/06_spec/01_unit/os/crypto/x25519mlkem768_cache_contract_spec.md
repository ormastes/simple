# X25519mlkem768 Cache Contract Specification

> Tests covering X25519MLKEM768 cache boundary contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Cache Contract Specification

## Scenarios

### X25519MLKEM768 cache boundary contract

#### should NFR-012 change the configuration digest for every selectable input

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should NFR-012 change the configuration digest for every selectable input
- Resolve configurations that differ by exactly one selectable input


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should NFR-012 change the configuration digest for every selectable input")
step("Resolve configurations that differ by exactly one selectable input")
val baseline = _configuration_digest(_cache_config(
    X25519MlKem768Backend.ScalarCpu,
    X25519MlKem768SelectionMode.Suggest, 1, 1))
val backend = _configuration_digest(_cache_config(
    X25519MlKem768Backend.Automatic,
    X25519MlKem768SelectionMode.Suggest, 1, 1))
val selection = _configuration_digest(_cache_config(
    X25519MlKem768Backend.ScalarCpu,
    X25519MlKem768SelectionMode.Require, 1, 1))
val minimum_batch = _configuration_digest(_cache_config(
    X25519MlKem768Backend.ScalarCpu,
    X25519MlKem768SelectionMode.Suggest, 2, 2))
val batch_size = _configuration_digest(_cache_config(
    X25519MlKem768Backend.ScalarCpu,
    X25519MlKem768SelectionMode.Suggest, 1, 2))
expect(baseline.len()).to_be_greater_than(0)
expect(backend == baseline).to_be(false)
expect(selection == baseline).to_be(false)
expect(minimum_batch == baseline).to_be(false)
expect(batch_size == baseline).to_be(false)
```

</details>

#### should NFR-012 reject stale semantic and profile versions

- should NFR-012 reject stale semantic and profile versions
- Present stale implementation and profile versions to the resolver


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should NFR-012 reject stale semantic and profile versions")
step("Present stale implementation and profile versions to the resolver")
val current = _cache_config(
    X25519MlKem768Backend.ScalarCpu,
    X25519MlKem768SelectionMode.Suggest, 1, 1)
val stale_semantic = X25519MlKem768Config(
    implementation_version: "stale-semantic-version",
    profile_version: current.profile_version,
    requested_backend: current.requested_backend,
    selection_mode: current.selection_mode,
    verification_policy: current.verification_policy,
    minimum_batch: current.minimum_batch,
    batch_size: current.batch_size)
val stale_profile = X25519MlKem768Config(
    implementation_version: current.implementation_version,
    profile_version: "stale-profile-version",
    requested_backend: current.requested_backend,
    selection_mode: current.selection_mode,
    verification_policy: current.verification_policy,
    minimum_batch: current.minimum_batch,
    batch_size: current.batch_size)
expect(x25519_mlkem768_resolve_backend(
    stale_semantic, "cache-contract").is_err()).to_be(true)
expect(x25519_mlkem768_resolve_backend(
    stale_profile, "cache-contract").is_err()).to_be(true)
```

</details>

#### should NFR-012 exclude external process launchers from every executor path

- should NFR-012 exclude external process launchers from every executor path
- Resolve each device-backend candidate through the executor policy
- Confirm every resolved path is an in-process candidate with no device execution
   - Expected: ev.executor_identity equals `cuda-candidate`
   - Expected: ev.kernel_invocations equals `0`
   - Expected: ev.executor_identity equals `metal-candidate`
   - Expected: ev.kernel_invocations equals `0`
   - Expected: ev.executor_identity equals `vulkan-candidate`
   - Expected: ev.kernel_invocations equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should NFR-012 exclude external process launchers from every executor path")
step("Resolve each device-backend candidate through the executor policy")
step("Confirm every resolved path is an in-process candidate with no device execution")
# oracle: candidate resolution must stay in-process — no kernel runs,
# no submit, no readback, executor identity names the in-process candidate
val cuda = x25519_mlkem768_resolve_cuda_candidate(_cache_config(
    X25519MlKem768Backend.Cuda,
    X25519MlKem768SelectionMode.Require, 1, 1), "cache-contract")
val metal = x25519_mlkem768_resolve_metal_candidate(_cache_config(
    X25519MlKem768Backend.Metal,
    X25519MlKem768SelectionMode.Require, 1, 1), "cache-contract")
val vulkan = x25519_mlkem768_resolve_vulkan_candidate(_cache_config(
    X25519MlKem768Backend.Vulkan,
    X25519MlKem768SelectionMode.Require, 1, 1), "cache-contract")
for result in [cuda, metal, vulkan]:
    expect(result.is_ok()).to_be(true)
match cuda:
    case Ok(ev):
        expect(ev.executor_identity).to_equal("cuda-candidate")
        expect(ev.kernel_invocations).to_equal(0)
        expect(ev.compiled).to_be(false)
        expect(ev.submitted).to_be(false)
    case Err(msg):
        fail_test("cuda candidate resolution failed: {msg}")
match metal:
    case Ok(ev):
        expect(ev.executor_identity).to_equal("metal-candidate")
        expect(ev.kernel_invocations).to_equal(0)
        expect(ev.submitted).to_be(false)
    case Err(msg):
        fail_test("metal candidate resolution failed: {msg}")
match vulkan:
    case Ok(ev):
        expect(ev.executor_identity).to_equal("vulkan-candidate")
        expect(ev.kernel_invocations).to_equal(0)
        expect(ev.submitted).to_be(false)
    case Err(msg):
        fail_test("vulkan candidate resolution failed: {msg}")
```

</details>

#### should NFR-012 guard device compilation and module load by session state

- should NFR-012 guard device compilation and module load by session state
- Resolve candidates outside any live device session
- Confirm no compilation, submit, fence, or readback is claimed and cross-backend requests are rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should NFR-012 guard device compilation and module load by session state")
step("Resolve candidates outside any live device session")
step("Confirm no compilation, submit, fence, or readback is claimed and cross-backend requests are rejected")
# oracle: without an initialized session the evidence must show no
# compiled/submitted/fence/readback activity, and a backend mismatch is refused
val cuda = x25519_mlkem768_resolve_cuda_candidate(_cache_config(
    X25519MlKem768Backend.Cuda,
    X25519MlKem768SelectionMode.Require, 1, 1), "cache-contract")
match cuda:
    case Ok(ev):
        expect(ev.compiled).to_be(false)
        expect(ev.submitted).to_be(false)
        expect(ev.fence_completed).to_be(false)
        expect(ev.device_readback).to_be(false)
        expect(ev.oracle_match).to_be(false)
    case Err(msg):
        fail_test("cuda candidate resolution failed: {msg}")
val wrong_backend = x25519_mlkem768_resolve_cuda_candidate(_cache_config(
    X25519MlKem768Backend.Vulkan,
    X25519MlKem768SelectionMode.Require, 1, 1), "cache-contract")
expect(wrong_backend.is_err()).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_cache_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 cache boundary contract.
- X25519MLKEM768 cache boundary contract

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b4bff703765c972cc902f2652267866432e8020f59a83a5a262de77c11a3724f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b4bff703765c972cc902f2652267866432e8020f59a83a5a262de77c11a3724f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b4bff703765c972cc902f2652267866432e8020f59a83a5a262de77c11a3724f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/01_unit/os/crypto/x25519mlkem768_cache_contract_spec.spl
mirror: doc/06_spec/01_unit/os/crypto/x25519mlkem768_cache_contract_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=80 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/crypto/x25519mlkem768_cache_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/crypto/x25519mlkem768_cache_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/crypto/x25519mlkem768_cache_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/crypto/x25519mlkem768_cache_contract_spec.spl:48:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should NFR-012 change the configuration digest for every selectable input' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_cache_contract_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should NFR-012 change the configuration digest for every selectable input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_cache_contract_spec.spl:73:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should NFR-012 reject stale semantic and profile versions' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_cache_contract_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should NFR-012 reject stale semantic and profile versions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_cache_contract_spec.spl:101:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should NFR-012 exclude external process launchers from every executor path' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_cache_contract_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should NFR-012 exclude external process launchers from every executor path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_cache_contract_spec.spl:142:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should NFR-012 guard device compilation and module load by session state' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
