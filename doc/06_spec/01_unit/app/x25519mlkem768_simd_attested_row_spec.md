# X25519mlkem768 Simd Attested Row Specification

> Tests covering X25519MLKEM768 SIMD observed final-row adapter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Simd Attested Row Specification

## Scenarios

### X25519MLKEM768 SIMD observed final-row adapter

#### promotes one public AVX2 observation only after attestation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- promotes one public AVX2 observation only after attestation
- Compose the raw non-promotable observation into one executed row


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("promotes one public AVX2 observation only after attestation")
step("Compose the raw non-promotable observation into one executed row")
val result = x25519_mlkem768_compose_simd_attested_matrix_row(
    _binding("4" * 64, "5" * 64, "5" * 64),
    _observation("4" * 64, "5" * 64, "5" * 64), _performance())
expect(result.is_ok()).to_be(true)
expect(result.unwrap().execution.promotion_eligible).to_be(true)
```

</details>

#### rejects raw promotion, binding-attestation mismatch, and ISA drift

- rejects raw promotion, binding-attestation mismatch, and ISA drift


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects raw promotion, binding-attestation mismatch, and ISA drift")
var promoted = _observation("4" * 64, "5" * 64, "5" * 64)
promoted.raw_receipt.promotion_eligible = true
_expect_err(x25519_mlkem768_compose_simd_attested_matrix_row(
    _binding("4" * 64, "5" * 64, "5" * 64), promoted, _performance()),
    "avx2-public-observation-invalid")
var mismatched = _performance()
mismatched.session_id = "different-session"
_expect_err(x25519_mlkem768_compose_simd_attested_matrix_row(
    _binding("4" * 64, "5" * 64, "5" * 64),
    _observation("4" * 64, "5" * 64, "5" * 64), mismatched),
    "avx2-performance-attestation-invalid")
var wrong_arch = _binding("4" * 64, "5" * 64, "5" * 64)
wrong_arch.host_arch = "aarch64"
_expect_err(x25519_mlkem768_compose_simd_attested_matrix_row(
    wrong_arch, _observation("4" * 64, "5" * 64, "5" * 64), _performance()),
    "avx2-receipt-binding-invalid")
```

</details>

#### rejects altered public sets wires and operation-output digests

- rejects altered public sets wires and operation-output digests


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects altered public sets wires and operation-output digests")
var altered_set = _observation("4" * 64, "5" * 64, "5" * 64)
altered_set.set_a.first_output_sha256 = "0" * 64
_expect_err(x25519_mlkem768_compose_simd_attested_matrix_row(
    _binding("4" * 64, "5" * 64, "5" * 64), altered_set, _performance()),
    "simd-attested-public-set-mismatch")
var altered_wire = _observation("4" * 64, "5" * 64, "5" * 64)
altered_wire.client_share_sha256 = "0" * 64
_expect_err(x25519_mlkem768_compose_simd_attested_matrix_row(
    _binding("4" * 64, "5" * 64, "5" * 64), altered_wire, _performance()),
    "simd-attested-public-wire-mismatch")
_expect_err(x25519_mlkem768_compose_simd_attested_matrix_row(
    _binding("4" * 64, "5" * 64, "5" * 64),
    _observation("4" * 64, "5" * 64, "6" * 64), _performance()),
    "simd-attested-operation-output-mismatch")
```

</details>

#### rejects a substituted CLI backend before observing a raw receipt

- rejects a substituted CLI backend before observing a raw receipt
- Keep final evidence bound to the typed SIMD receipt backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a substituted CLI backend before observing a raw receipt")
step("Keep final evidence bound to the typed SIMD receipt backend")
val cli = X25519MlKem768EvidenceCli(
    fixture_manifest: "ignored-by-typed-orchestrator",
    fixture_source: "ignored-by-typed-orchestrator",
    runner_source: "ignored-by-typed-orchestrator",
    backend: X25519MlKem768EvidenceBackend.Neon,
    mode: X25519MlKem768EvidenceMode.Native,
    scope: X25519MlKem768EvidenceScope.FullOperation, batch_size: 1)
val admission = X25519MlKem768SimdAdmission(
    encoded_provenance: "", actual_binary_sha256: "",
    actual_provenance_sha256: "")
_expect_err(x25519_mlkem768_observe_and_compose_simd_attested_matrix_row(
    cli, admission, _binding("4" * 64, "5" * 64, "5" * 64),
    _performance()), "simd-final-cli-binding-backend-mismatch")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/x25519mlkem768_simd_attested_row_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 SIMD observed final-row adapter.
- X25519MLKEM768 SIMD observed final-row adapter

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

- `REQ-SSPEC-UNIT`
- `REQ-003`
- `REQ-013`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a76995e28d740d27dc8b2fc5e0a1c3c9b6fc7da43e67f48c26690697ce6ef05a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a76995e28d740d27dc8b2fc5e0a1c3c9b6fc7da43e67f48c26690697ce6ef05a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a76995e28d740d27dc8b2fc5e0a1c3c9b6fc7da43e67f48c26690697ce6ef05a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/x25519mlkem768_simd_attested_row_spec.spl
mirror: doc/06_spec/01_unit/app/x25519mlkem768_simd_attested_row_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/app/x25519mlkem768_simd_attested_row_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/x25519mlkem768_simd_attested_row_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/x25519mlkem768_simd_attested_row_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/x25519mlkem768_simd_attested_row_spec.spl:175:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'promotes one public AVX2 observation only after attestation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/x25519mlkem768_simd_attested_row_spec.spl:185:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects raw promotion, binding-attestation mismatch, and ISA drift' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/x25519mlkem768_simd_attested_row_spec.spl:205:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects altered public sets wires and operation-output digests' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
