# Live Kms Transport Specification

> Tests covering live KMS transport coverage.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Live Kms Transport Specification

## Scenarios

### live KMS transport coverage

#### AWS KMS sign executes only when explicitly enabled

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AWS KMS sign executes only when explicitly enabled
   - Expected: _ok_or_skipped(_aws_live_sign_status()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AWS KMS sign executes only when explicitly enabled")
expect(_ok_or_skipped(_aws_live_sign_status())).to_equal(true)
```

</details>

#### GCP Cloud KMS sign executes only when explicitly enabled

- GCP Cloud KMS sign executes only when explicitly enabled
   - Expected: _ok_or_skipped(_gcp_live_sign_status()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("GCP Cloud KMS sign executes only when explicitly enabled")
expect(_ok_or_skipped(_gcp_live_sign_status())).to_equal(true)
```

</details>

#### Azure Key Vault sign executes only when explicitly enabled

- Azure Key Vault sign executes only when explicitly enabled
   - Expected: _ok_or_skipped(_azure_live_sign_status()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("Azure Key Vault sign executes only when explicitly enabled")
expect(_ok_or_skipped(_azure_live_sign_status())).to_equal(true)
```

</details>

#### PKCS11 HSM gateway sign executes only when explicitly enabled

- PKCS11 HSM gateway sign executes only when explicitly enabled
   - Expected: _ok_or_skipped(_hsm_live_sign_status()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("PKCS11 HSM gateway sign executes only when explicitly enabled")
expect(_ok_or_skipped(_hsm_live_sign_status())).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/integration/lib/security/live_kms_transport_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering live KMS transport coverage.
- live KMS transport coverage

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cb8f78fe850e126ac3bf095089330e90fd0fd5b2deeb790ff0deecb135f668cd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cb8f78fe850e126ac3bf095089330e90fd0fd5b2deeb790ff0deecb135f668cd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cb8f78fe850e126ac3bf095089330e90fd0fd5b2deeb790ff0deecb135f668cd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/lib/security/live_kms_transport_spec.spl
mirror: doc/06_spec/integration/lib/security/live_kms_transport_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/lib/security/live_kms_transport_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/lib/security/live_kms_transport_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/lib/security/live_kms_transport_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AWS KMS sign executes only when explicitly enabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/lib/security/live_kms_transport_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'GCP Cloud KMS sign executes only when explicitly enabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/lib/security/live_kms_transport_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Azure Key Vault sign executes only when explicitly enabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
