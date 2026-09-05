# Formal Gate Collectors Specification

> Tests covering FV2 verification-truthfulness gate collector.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Formal Gate Collectors Specification

## Scenarios

### FV2 verification-truthfulness gate collector

#### keeps the public receipt finalizer diagnostic-only

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the public receipt finalizer diagnostic-only
   - Expected: collection.gate_evidence.status.name() equals `failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the public receipt finalizer diagnostic-only")
val content = "caller-owned-receipt"
val raw = FormalDeliveryReceiptFileV1(sha256_text(content), content)
val collection = finalize_formal_gate_collection_v2(
    FormalDeliveryGateV1.VerificationTruthfulness,
    sha256_text("semantic-evidence"), [raw])
expect(collection.gate_evidence.status.name()).to_equal("failed")
expect(collection.gate_evidence.diagnostic).to_contain(
    "GATE-FINALIZER-AUTHORITY")
expect(collection.receipt_files.is_empty()).to_be(true)

val malformed = FormalDeliveryReceiptFileV1(
    sha256_text("other-content"), content)
expect(finalize_formal_gate_collection_v2(
    FormalDeliveryGateV1.VerificationTruthfulness,
    sha256_text("semantic-evidence"), [malformed]).gate_evidence.diagnostic).to_contain(
    "RECEIPT-FINALIZE")
```

</details>

#### does not promote caller-constructed closed proof evidence

- does not promote caller-constructed closed proof evidence
   - Expected: collection.gate_evidence.status.name() equals `failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not promote caller-constructed closed proof evidence")
val collection = collect_verification_truthfulness_gate_v1([
    truth_item()])
expect(collection.gate_evidence.status.name()).to_equal("failed")
expect(collection.gate_evidence.diagnostic).to_contain(
    "TRUTH-EXECUTION-AUTHORITY")
expect(collection.gate_evidence.receipt_hashes.is_empty()).to_be(true)
expect(collection.receipt_files.is_empty()).to_be(true)
```

</details>

#### rejects a transitive sorry axiom rather than publishing passing evidence

- rejects a transitive sorry axiom rather than publishing passing evidence
   - Expected: collection.gate_evidence.status.name() equals `failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a transitive sorry axiom rather than publishing passing evidence")
val root = "Proofs.unsafe"
val audit = audit_lean_axiom_report(
    "'Proofs.unsafe' depends on axioms: [sorryAx]", [root], [])
val replay = truth_replay()
val trust = TrustManifestV1(["propext", "Classical.choice", "Quot.sound"],
    [], [], [], [], [])
val key = VerificationCacheKeyV1(sha256_text("vir"), sha256_text("contract"),
    sha256_text("weave"), sha256_text("macro"), [sha256_text("dependency")],
    "effects-v1", "compiler-v1", "x86_64-unknown-linux-gnu", "4.33.0",
    sha256_text("mathlib"), ["lean4checker-v1", "nanoda-v1"],
    sha256_text("tactics"), sha256_text("trust-policy"), "verified")
val receipt = ProofReceiptV1(root, FormalStatus.ModelProven,
    key.hash(), sha256_text("artifact"), [],
    trust_audit_hash_v1(audit, sha256_text("artifact")),
    sha256_text(trust.canonical_text()), "", replay.hash())
val collection = collect_verification_truthfulness_gate_v1([
    TruthfulnessProofEvidenceV1(receipt, key,
        "'Proofs.unsafe' depends on axioms: [sorryAx]",
        sha256_text("artifact"), trust, replay)])
expect(collection.gate_evidence.status.name()).to_equal("failed")
expect(collection.gate_evidence.diagnostic).to_contain("AXIOMS")
expect(collection.receipt_files.is_empty()).to_be(true)
```

</details>

#### rejects weak identities replay drift and duplicate roots

- rejects weak identities replay drift and duplicate roots


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects weak identities replay drift and duplicate roots")
var weak = truth_item()
weak.receipt.cache_key_hash = "polynomial-checksum"
expect(collect_verification_truthfulness_gate_v1([weak]).gate_evidence.diagnostic).to_contain("CACHE")
var drift = truth_item()
drift.receipt.independent_replay_hash = sha256_text("other-replay")
expect(collect_verification_truthfulness_gate_v1([drift]).gate_evidence.diagnostic).to_contain("REPLAY-BINDING")
expect(collect_verification_truthfulness_gate_v1([
    truth_item(), truth_item()]).gate_evidence.diagnostic).to_contain(
    "DUPLICATE")
```

</details>

#### rejects an axiom report for a different theorem root

- rejects an axiom report for a different theorem root


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an axiom report for a different theorem root")
var substituted = truth_item("Proofs.claimed")
substituted.retained_axiom_report =
    "'Proofs.other' does not depend on any axioms"
expect(collect_verification_truthfulness_gate_v1([
    substituted]).gate_evidence.diagnostic).to_contain("AXIOMS")
```

</details>

#### rejects an axiom report retained for another artifact

- rejects an axiom report retained for another artifact


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an axiom report retained for another artifact")
var substituted = truth_item()
substituted.axiom_report_artifact_hash = sha256_text("other-artifact")
expect(collect_verification_truthfulness_gate_v1([
    substituted]).gate_evidence.diagnostic).to_contain("AXIOM-ARTIFACT")
```

</details>

#### rejects a hidden environmental trust assumption

- rejects a hidden environmental trust assumption


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a hidden environmental trust assumption")
var open = truth_item()
open.trust_manifest = TrustManifestV1([], [], [], [], [],
    ["device behaves correctly"])
expect(collect_verification_truthfulness_gate_v1([
    open]).gate_evidence.diagnostic).to_contain("TRUST")
```

</details>

#### rejects cache or toolchain substitution

- rejects cache or toolchain substitution


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects cache or toolchain substitution")
var substituted = truth_item()
substituted.cache_key.lean_version = "different-lean"
expect(collect_verification_truthfulness_gate_v1([
    substituted]).gate_evidence.diagnostic).to_contain("CACHE")
```

</details>

#### rejects a cache key without a verified Mathlib identity

- rejects a cache key without a verified Mathlib identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a cache key without a verified Mathlib identity")
var substituted = truth_item()
substituted.cache_key.mathlib_hash = ""
substituted.receipt.cache_key_hash = substituted.cache_key.hash()
expect(collect_verification_truthfulness_gate_v1([
    substituted]).gate_evidence.diagnostic).to_contain("CACHE")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/verification/formal_gate_collectors_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FV2 verification-truthfulness gate collector.
- FV2 verification-truthfulness gate collector

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ad84858140b7654007822f0c9f98876342385ffdca035508e02afafccc3e5850`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ad84858140b7654007822f0c9f98876342385ffdca035508e02afafccc3e5850`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ad84858140b7654007822f0c9f98876342385ffdca035508e02afafccc3e5850`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/verification/formal_gate_collectors_spec.spl
mirror: doc/06_spec/01_unit/compiler/verification/formal_gate_collectors_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/verification/formal_gate_collectors_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/verification/formal_gate_collectors_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/verification/formal_gate_collectors_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the public receipt finalizer diagnostic-only' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/verification/formal_gate_collectors_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not promote caller-constructed closed proof evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/verification/formal_gate_collectors_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a transitive sorry axiom rather than publishing passing evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
