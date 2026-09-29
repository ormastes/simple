# Verified Release Gate Specification

> Tests covering Verification 2.0 fail-closed release gate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Verified Release Gate Specification

## Scenarios

### Verification 2.0 fail-closed release gate

#### binds signer authority to the canonical full policy SHA-256

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- binds signer authority to the canonical full policy SHA-256


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("binds signer authority to the canonical full policy SHA-256")
val policy = verified_release_policy_v2()
val changed = verified_release_policy_v2("different-runtime")
val authority = assurance_policy_authority_hash_v3(policy)
expect(sha256_lower_hex_valid(authority)).to_be(true)
expect(authority == assurance_policy_authority_hash_v3(changed)).to_be(false)
```

</details>

#### requires a resolved V2 verified policy at the typed release boundary

- requires a resolved V2 verified policy at the typed release boundary
   - Expected: downgraded.passed() is false
   - Expected: mismatched.passed() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("requires a resolved V2 verified policy at the typed release boundary")
val verified = ResolvedAssurancePolicyV2(AssuranceStrictnessV2.Verified,
    "nogc_async_mut_noalloc", AssuranceGrade.NoGrade,
    AssuranceConvention.NoConvention)
val critical = ResolvedAssurancePolicyV2(AssuranceStrictnessV2.Critical,
    "nogc_async_mut_noalloc", AssuranceGrade.NoGrade,
    AssuranceConvention.NoConvention)
expect(evaluate_verified_release_v2(VerifiedReleaseEvidenceV2(
    verified, release_evidence())).passed()).to_equal(true)
val downgraded = evaluate_verified_release_v2(VerifiedReleaseEvidenceV2(
    critical, release_evidence()))
expect(downgraded.passed()).to_equal(false)
expect(downgraded.diagnostic_codes).to_contain("FV2-RELEASE-POLICY-V2")
val mismatched = evaluate_verified_release_v2(VerifiedReleaseEvidenceV2(
    verified, release_evidence(profile: "critical")))
expect(mismatched.passed()).to_equal(false)
expect(mismatched.diagnostic_codes).to_contain("FV2-RELEASE-POLICY-BINDING")
```

</details>

#### signs the V2 policy identity together with the release evidence

- signs the V2 policy identity together with the release evidence
   - Expected: accepted.admitted is true
   - Expected: drifted.admitted is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("signs the V2 policy identity together with the release evidence")
val policy = ResolvedAssurancePolicyV2(AssuranceStrictnessV2.Verified,
    "nogc_async_mut_noalloc", AssuranceGrade.NoGrade,
    AssuranceConvention.NoConvention)
val evidence = VerifiedReleaseEvidenceV2(policy, release_evidence())
val payload = evaluate_verified_release_v2(evidence).evidence_hash
val signature = SignatureVerificationReceiptV1(payload, "release-key",
    "pure-ed25519-v1", sha256_text("signature-evidence"), true)
val accepted = validate_signed_verified_release_bundle_v2(
    SignedVerifiedReleaseBundleV2(evidence, payload, "release-key",
        ReleaseSignatureVerificationV1("release-key", sha256_text("public-key"),
            signature)), [ApprovedReleaseSignerV1("release-key",
            sha256_text("public-key"))])
expect(accepted.admitted).to_equal(true)
val changed_policy = ResolvedAssurancePolicyV2(AssuranceStrictnessV2.Verified,
    "different-runtime", AssuranceGrade.NoGrade,
    AssuranceConvention.NoConvention)
val drifted = validate_signed_verified_release_bundle_v2(
    SignedVerifiedReleaseBundleV2(VerifiedReleaseEvidenceV2(changed_policy,
        release_evidence()), payload, "release-key",
        ReleaseSignatureVerificationV1("release-key", sha256_text("public-key"),
            signature)), [ApprovedReleaseSignerV1("release-key",
            sha256_text("public-key"))])
expect(drifted.admitted).to_equal(false)
expect(drifted.diagnostic).to_contain("PAYLOAD-V2")
```

</details>

#### passes only a complete exact artifact-verified evidence set

- passes only a complete exact artifact-verified evidence set
   - Expected: decision.passed() is true
   - Expected: decision.diagnostic_codes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("passes only a complete exact artifact-verified evidence set")
val decision = evaluate_verified_release_v1(release_evidence())
expect(decision.passed()).to_equal(true)
expect(decision.diagnostic_codes.len()).to_equal(0)
```

</details>

#### uses unambiguous framing for list-valued evidence identities

- uses unambiguous framing for list-valued evidence identities


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses unambiguous framing for list-valued evidence identities")
var left = release_evidence()
var right = release_evidence()
left.proof_receipt_hashes = [sha256_text("a,b"), sha256_text("c")]
right.proof_receipt_hashes = [sha256_text("a"), sha256_text("b,c")]
expect(release_evidence_hash_v1(left) ==
    release_evidence_hash_v1(right)).to_equal(false)
```

</details>

#### rejects every non-proof external tool outcome

- rejects every non-proof external tool outcome
   - Expected: decision.passed() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects every non-proof external tool outcome")
val outcomes = [ReleaseEvidenceOutcomeV1.Unknown,
    ReleaseEvidenceOutcomeV1.Timeout,
    ReleaseEvidenceOutcomeV1.MissingTool,
    ReleaseEvidenceOutcomeV1.ToolFailure,
    ReleaseEvidenceOutcomeV1.EnvironmentFailure]
for outcome in outcomes:
    val decision = evaluate_verified_release_v1(
        release_evidence(outcome))
    expect(decision.passed()).to_equal(false)
expect(evaluate_verified_release_v1(release_evidence(
    ReleaseEvidenceOutcomeV1.Unknown)).diagnostic_codes).to_contain(
    "FV2-RELEASE-UNKNOWN")
expect(evaluate_verified_release_v1(release_evidence(
    ReleaseEvidenceOutcomeV1.Timeout)).diagnostic_codes).to_contain(
    "FV2-RELEASE-TIMEOUT")
expect(evaluate_verified_release_v1(release_evidence(
    ReleaseEvidenceOutcomeV1.MissingTool)).diagnostic_codes).to_contain(
    "FV2-RELEASE-MISSING-TOOL")
```

</details>

#### rejects stale unsupported warning and environment counts

- rejects stale unsupported warning and environment counts


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects stale unsupported warning and environment counts")
expect(evaluate_verified_release_v1(release_evidence(
    unsupported: 1)).diagnostic_codes).to_contain(
    "FV2-RELEASE-UNSUPPORTED")
expect(evaluate_verified_release_v1(release_evidence(
    stale: 1)).diagnostic_codes).to_contain("FV2-RELEASE-STALE")
expect(evaluate_verified_release_v1(release_evidence(
    warnings: 1)).diagnostic_codes).to_contain(
    "FV2-RELEASE-WARNING-CONTROL")
expect(evaluate_verified_release_v1(release_evidence(
    environment_errors: 1)).diagnostic_codes).to_contain(
    "FV2-RELEASE-ENVIRONMENT-COUNT")
expect(evaluate_verified_release_v1(release_evidence(
    delivery_manifest: "")).diagnostic_codes).to_contain(
    "FV2-RELEASE-DELIVERY-GATES")
```

</details>

#### rejects model-only status profile drift and artifact mismatch

- rejects model-only status profile drift and artifact mismatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects model-only status profile drift and artifact mismatch")
expect(evaluate_verified_release_v1(release_evidence(
    artifact_status: FormalStatus.ModelProven)).diagnostic_codes).to_contain(
    "FV2-RELEASE-ARTIFACT-STATUS")
expect(evaluate_verified_release_v1(release_evidence(
    reachable_status: FormalStatus.Stale)).diagnostic_codes).to_contain(
    "FV2-RELEASE-CLOSURE-STATUS")
expect(evaluate_verified_release_v1(release_evidence(
    profile: "critical")).diagnostic_codes).to_contain(
    "FV2-RELEASE-PROFILE")
expect(evaluate_verified_release_v1(release_evidence(
    evidence_artifact: "other")).diagnostic_codes).to_contain(
    "FV2-RELEASE-ARTIFACT-IDENTITY")
```

</details>

#### requires an explicit bounded TCB for trusted boundaries

- requires an explicit bounded TCB for trusted boundaries
   - Expected: missing.passed() is false
   - Expected: bounded.passed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("requires an explicit bounded TCB for trusted boundaries")
val missing = evaluate_verified_release_v1(release_evidence(
    outcome: ReleaseEvidenceOutcomeV1.ApprovedExternalTcb,
    reachable_status: FormalStatus.TrustedBoundary))
expect(missing.passed()).to_equal(false)
expect(missing.diagnostic_codes).to_contain("FV2-RELEASE-TCB-MANIFEST")
val bounded = evaluate_verified_release_v1(release_evidence(
    outcome: ReleaseEvidenceOutcomeV1.ApprovedExternalTcb,
    reachable_status: FormalStatus.TrustedBoundary,
    bounded_tcb: sha256_text("bounded-tcb-manifest")))
expect(bounded.passed()).to_equal(true)
```

</details>

#### admits only a signature bound to exact release evidence and policy

- admits only a signature bound to exact release evidence and policy
   - Expected: accepted.admitted is true
   - Expected: accepted.release_decision.passed() is true
   - Expected: accepted.bundle_hash == "" is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("admits only a signature bound to exact release evidence and policy")
val evidence = release_evidence()
val payload = release_evidence_hash_v1(evidence)
val signature = SignatureVerificationReceiptV1(payload, "release-key",
    "pure-ed25519-v1", sha256_text("signature-evidence"), true)
val bundle = SignedVerifiedReleaseBundleV1(evidence, payload,
    "release-key", ReleaseSignatureVerificationV1("release-key",
        sha256_text("public-key"), signature))
val accepted = validate_signed_verified_release_bundle_v1(bundle,
    [ApprovedReleaseSignerV1("release-key", sha256_text("public-key"))])
expect(accepted.admitted).to_equal(true)
expect(accepted.release_decision.passed()).to_equal(true)
expect(accepted.bundle_hash == "").to_equal(false)
```

</details>

#### rejects payload drift failed signature and unapproved signer

- rejects payload drift failed signature and unapproved signer


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects payload drift failed signature and unapproved signer")
val evidence = release_evidence()
val payload = release_evidence_hash_v1(evidence)
val valid = SignatureVerificationReceiptV1(payload, "release-key",
    "pure-ed25519-v1", sha256_text("signature-evidence"), true)
val drifted = validate_signed_verified_release_bundle_v1(
    SignedVerifiedReleaseBundleV1(evidence, "other", "release-key",
        ReleaseSignatureVerificationV1("release-key", sha256_text("public-key"),
            valid)), [ApprovedReleaseSignerV1("release-key", sha256_text("public-key"))])
expect(drifted.diagnostic).to_contain("PAYLOAD")
val failed = SignatureVerificationReceiptV1(payload, "release-key",
    "pure-ed25519-v1", sha256_text("signature-evidence"), false)
expect(validate_signed_verified_release_bundle_v1(
    SignedVerifiedReleaseBundleV1(evidence, payload, "release-key",
        ReleaseSignatureVerificationV1("release-key", sha256_text("public-key"),
            failed)), [ApprovedReleaseSignerV1("release-key",
            sha256_text("public-key"))]).admitted).to_equal(false)
val unapproved = validate_signed_verified_release_bundle_v1(
    SignedVerifiedReleaseBundleV1(evidence, payload, "release-key",
        ReleaseSignatureVerificationV1("release-key", sha256_text("public-key"),
            valid)), [ApprovedReleaseSignerV1("other-key", sha256_text("public-key"))])
expect(unapproved.diagnostic).to_contain("POLICY")
```

</details>

#### rejects signer-name reuse with a different public key

- rejects signer-name reuse with a different public key
   - Expected: decision.admitted is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects signer-name reuse with a different public key")
val evidence = release_evidence()
val payload = release_evidence_hash_v1(evidence)
val receipt = SignatureVerificationReceiptV1(payload, "release-key",
    "pure-ed25519-v1", sha256_text("signature-evidence"), true)
val bundle = SignedVerifiedReleaseBundleV1(evidence, payload,
    "release-key", ReleaseSignatureVerificationV1("release-key",
        sha256_text("attacker-key"), receipt))
val decision = validate_signed_verified_release_bundle_v1(bundle,
    [ApprovedReleaseSignerV1("release-key", sha256_text("approved-key"))])
expect(decision.admitted).to_equal(false)
expect(decision.diagnostic).to_contain("POLICY")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/assurance/verified_release_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Verification 2.0 fail-closed release gate.
- Verification 2.0 fail-closed release gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1cf032bea6d5b0fb654bd8f23faead54aa3bc1db9409ca1b0169d9e28aca7806`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1cf032bea6d5b0fb654bd8f23faead54aa3bc1db9409ca1b0169d9e28aca7806`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1cf032bea6d5b0fb654bd8f23faead54aa3bc1db9409ca1b0169d9e28aca7806`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **93/100**; effective score: **93/100**; blockers: **0**.

SSpec documentization score: 93/100
source: test/01_unit/compiler/assurance/verified_release_gate_spec.spl
mirror: doc/06_spec/01_unit/compiler/assurance/verified_release_gate_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/assurance/verified_release_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/assurance/verified_release_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/assurance/verified_release_gate_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/assurance/verified_release_gate_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds signer authority to the canonical full policy SHA-256' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
