# X25519mlkem768 Core Provider Negative Specification

> Tests covering X25519MLKEM768 core provider negative branches.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Core Provider Negative Specification

## Scenarios

### X25519MLKEM768 core provider negative branches

#### should propagate a deterministic forward-provider failure from key generation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should propagate a deterministic forward-provider failure from key generation
- Inject an explicit forward NTT error before polynomial splitting


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should propagate a deterministic forward-provider failure from key generation")
step("Inject an explicit forward NTT error before polynomial splitting")
val provider = DeterministicFaultNttProvider.create(
    "fixture-forward-failure", "", false)
match ml_kem_keygen_checked_provider(
        _core_zero32(), _core_zero32(), provider):
    case Ok(_): fail("key generation swallowed the provider failure")
    case Err(reason): expect(reason).to_equal("fixture-forward-failure")
```

</details>

#### should reject a deterministic short accelerator output

- should reject a deterministic short accelerator output
- Return an empty forward batch for a nonempty polynomial request


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should reject a deterministic short accelerator output")
step("Return an empty forward batch for a nonempty polynomial request")
val provider = DeterministicFaultNttProvider.create("", "", true)
match ml_kem_keygen_checked_provider(
        _core_zero32(), _core_zero32(), provider):
    case Ok(_): fail("key generation accepted a short provider output")
    case Err(reason): expect(reason).to_equal(
        "ml-kem-accelerator-output-size-invalid")
```

</details>

#### should propagate a deterministic inverse-provider failure from encapsulation

- should propagate a deterministic inverse-provider failure from encapsulation
- Use valid scalar key material and fail the provider inverse batch


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should propagate a deterministic inverse-provider failure from encapsulation")
step("Use valid scalar key material and fail the provider inverse batch")
val (ek, _, _, message) = _core_valid_material()
val provider = DeterministicFaultNttProvider.create(
    "", "fixture-inverse-failure", false)
match ml_kem_encaps_checked_provider(ek, message, provider):
    case Ok(_): fail("encapsulation swallowed the provider failure")
    case Err(reason): expect(reason).to_equal("fixture-inverse-failure")
```

</details>

#### should propagate a deterministic inverse-provider failure from decapsulation

- should propagate a deterministic inverse-provider failure from decapsulation
- Use valid scalar ciphertext and fail the provider inverse batch


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should propagate a deterministic inverse-provider failure from decapsulation")
step("Use valid scalar ciphertext and fail the provider inverse batch")
val (_, dk, ciphertext, _) = _core_valid_material()
val provider = DeterministicFaultNttProvider.create(
    "", "fixture-inverse-failure", false)
match ml_kem_decaps_checked_provider(dk, ciphertext, provider):
    case Ok(_): fail("decapsulation swallowed the provider failure")
    case Err(reason): expect(reason).to_equal("fixture-inverse-failure")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_core_provider_negative_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 core provider negative branches.
- X25519MLKEM768 core provider negative branches

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

- Canonical SPipe generation for source `87d8177d6ed41f4b632c0a6385d82f6c19e9b592c1312c06773493a1066fb00e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `87d8177d6ed41f4b632c0a6385d82f6c19e9b592c1312c06773493a1066fb00e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `87d8177d6ed41f4b632c0a6385d82f6c19e9b592c1312c06773493a1066fb00e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/os/crypto/x25519mlkem768_core_provider_negative_spec.spl
mirror: doc/06_spec/01_unit/os/crypto/x25519mlkem768_core_provider_negative_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/crypto/x25519mlkem768_core_provider_negative_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/crypto/x25519mlkem768_core_provider_negative_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/crypto/x25519mlkem768_core_provider_negative_spec.spl:70:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should propagate a deterministic forward-provider failure from key generation' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_core_provider_negative_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should propagate a deterministic forward-provider failure from key generation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_core_provider_negative_spec.spl:81:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject a deterministic short accelerator output' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_core_provider_negative_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject a deterministic short accelerator output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_core_provider_negative_spec.spl:92:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should propagate a deterministic inverse-provider failure from encapsulation' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_core_provider_negative_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should propagate a deterministic inverse-provider failure from encapsulation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_core_provider_negative_spec.spl:103:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should propagate a deterministic inverse-provider failure from decapsulation' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
