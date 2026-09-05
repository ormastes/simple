# Formal Receipt Specification

> Tests covering Formal Verification 2.0 evidence receipts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Formal Receipt Specification

## Scenarios

### Formal Verification 2.0 evidence receipts

#### canonicalizes unordered cache inputs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- canonicalizes unordered cache inputs
   - Expected: left.diagnostic() equals ``
   - Expected: left.hash() equals `right.hash()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("canonicalizes unordered cache inputs")
val left = VerificationCacheKeyV1("vir", "contract", "weave", "macro", ["b", "a"], "effects-v1", "compiler-v1", "riscv64", "4.33.0", "mathlib", ["z3", "kissat"], "tactics", "trust", "verified")
val right = VerificationCacheKeyV1("vir", "contract", "weave", "macro", ["a", "b"], "effects-v1", "compiler-v1", "riscv64", "4.33.0", "mathlib", ["kissat", "z3"], "tactics", "trust", "verified")
expect(left.diagnostic()).to_equal("")
expect(left.hash()).to_equal(right.hash())
```

</details>

#### invalidates a verified cache identity when a semantic dimension changes

- invalidates a verified cache identity when a semantic dimension changes
   - Expected: left.hash() == right.hash() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("invalidates a verified cache identity when a semantic dimension changes")
val left = VerificationCacheKeyV1("vir", "contract", "weave-a", "macro", [], "effects-v1", "compiler-v1", "riscv64", "4.33.0", "mathlib", [], "tactics", "trust", "verified")
val right = VerificationCacheKeyV1("vir", "contract", "weave-b", "macro", [], "effects-v1", "compiler-v1", "riscv64", "4.33.0", "mathlib", [], "tactics", "trust", "verified")
expect(left.hash() == right.hash()).to_equal(false)
```

</details>

#### does not release an artifact without compiler and replay evidence

- does not release an artifact without compiler and replay evidence
   - Expected: incomplete.permits_verified_release() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not release an artifact without compiler and replay evidence")
val incomplete = ProofReceiptV1("Simple.safe", FormalStatus.ArtifactVerified,
    sha256_text("key"), sha256_text("artifact"), [], sha256_text("axioms"),
    sha256_text("trust"), "", "")
expect(incomplete.permits_verified_release()).to_equal(false)
expect(incomplete.diagnostic()).to_contain("COMPILER")
```

</details>

#### binds every proof receipt evidence dimension into its hash

- binds every proof receipt evidence dimension into its hash
   - Expected: first.hash() == second.hash() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binds every proof receipt evidence dimension into its hash")
val first = ProofReceiptV1("Simple.safe", FormalStatus.ModelProven,
    "key", "artifact", ["dep"], "axioms", "trust", "", "replay-a")
val second = ProofReceiptV1("Simple.safe", FormalStatus.ModelProven,
    "key", "artifact", ["dep"], "axioms", "trust", "", "replay-b")
expect(first.hash() == second.hash()).to_equal(false)
expect(first.canonical_text()).to_contain("ProofReceiptV1")
```

</details>

#### rejects a formerly valid artifact receipt after any cache-key edge changes

- rejects a formerly valid artifact receipt after any cache-key edge changes
   - Expected: receipt.reusable_for(old_key) is true
   - Expected: receipt.reusable_for(new_key) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a formerly valid artifact receipt after any cache-key edge changes")
val old_key = verified_cache_key()
val new_key = VerificationCacheKeyV1(old_key.vir_hash, old_key.contract_hash,
    sha256_text("weave-b"), old_key.macro_expansion_hash, old_key.dependency_hashes,
    old_key.effect_model_version, old_key.compiler_pass_version, old_key.target,
    old_key.lean_version, old_key.mathlib_hash, old_key.solver_versions,
    old_key.tactic_policy_hash, old_key.trust_policy_hash, "verified")
val artifact = sha256_text("artifact")
val certificate = valid_compiler_certificate()
val replay = valid_replay_closure(artifact)
val receipt = ProofReceiptV1("Simple.safe", FormalStatus.ArtifactVerified, old_key.hash(),
    artifact, [], sha256_text("axioms"), sha256_text("trust"),
    certificate.expected_certificate_hash(), replay.hash())
expect(receipt.reusable_for(old_key)).to_equal(true)
expect(receipt.reusable_for(new_key)).to_equal(false)
```

</details>

#### keeps bounded trust visible

- keeps bounded trust visible
   - Expected: manifest.is_closed() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps bounded trust visible")
val manifest = TrustManifestV1(["propext"], [], [], [], [], ["timer monotonic"])
expect(manifest.is_closed()).to_equal(false)
expect(manifest.canonical_text()).to_contain("timer monotonic")
```

</details>

#### requires the verified profile and a closed matching trust manifest

- requires the verified profile and a closed matching trust manifest
   - Expected: permits_closed_verified_release(verified, key, receipt, closed, certificate, replay) is true
   - Expected: permits_closed_verified_release(critical, key, receipt, closed, certificate, replay) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires the verified profile and a closed matching trust manifest")
val key = verified_cache_key()
val closed = TrustManifestV1(["propext"], [], [], [], [], [])
val certificate = valid_compiler_certificate()
val artifact = sha256_text("artifact")
val replay = valid_replay_closure(artifact)
val receipt = ProofReceiptV1("Simple.safe", FormalStatus.ArtifactVerified, key.hash(), artifact,
    [], sha256_text("axioms"), sha256_text(closed.canonical_text()),
    certificate.expected_certificate_hash(), replay.hash())
val verified = ResolvedAssurancePolicyV2(AssuranceStrictnessV2.Verified, "nogc_async_mut_noalloc", AssuranceGrade.NoGrade, AssuranceConvention.NoConvention)
val critical = ResolvedAssurancePolicyV2(AssuranceStrictnessV2.Critical, "nogc_async_mut_noalloc", AssuranceGrade.NoGrade, AssuranceConvention.NoConvention)
expect(permits_closed_verified_release(verified, key, receipt, closed, certificate, replay)).to_equal(true)
expect(permits_closed_verified_release(critical, key, receipt, closed, certificate, replay)).to_equal(false)
expect(permits_closed_verified_release(
    verified, key, receipt, closed, certificate,
    valid_replay_closure(sha256_text("other-artifact")))).to_equal(false)
```

</details>

#### rejects a receipt whose compiler edge is not the checked certificate

- rejects a receipt whose compiler edge is not the checked certificate
   - Expected: permits_closed_verified_release(verified, key, receipt, closed, certificate, replay) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a receipt whose compiler edge is not the checked certificate")
val key = verified_cache_key()
val closed = TrustManifestV1(["propext"], [], [], [], [], [])
val certificate = valid_compiler_certificate()
val artifact = sha256_text("artifact")
val replay = valid_replay_closure(artifact)
val receipt = ProofReceiptV1("Simple.safe", FormalStatus.ArtifactVerified, key.hash(), artifact,
    [], sha256_text("axioms"), sha256_text(closed.canonical_text()),
    sha256_text("another-edge"), replay.hash())
val verified = ResolvedAssurancePolicyV2(AssuranceStrictnessV2.Verified, "nogc_async_mut_noalloc", AssuranceGrade.NoGrade, AssuranceConvention.NoConvention)
expect(permits_closed_verified_release(verified, key, receipt, closed, certificate, replay)).to_equal(false)
```

</details>

#### rejects malformed semantic cache and receipt identities in the closed lane

- rejects malformed semantic cache and receipt identities in the closed lane


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects malformed semantic cache and receipt identities in the closed lane")
val malformed_key = VerificationCacheKeyV1("not-a-hash", sha256_text("contract"),
    sha256_text("weave"), sha256_text("macro"), [], "effects-v1", "compiler-v1",
    "riscv64", "4.33.0", sha256_text("mathlib"), [], sha256_text("tactics"),
    sha256_text("trust"), "verified")
expect(malformed_key.verified_identity_diagnostic()).to_contain("VIR-HASH")
val duplicated = VerificationCacheKeyV1(sha256_text("vir"), sha256_text("contract"),
    sha256_text("weave"), sha256_text("macro"), [sha256_text("dep"), sha256_text("dep")],
    "effects-v1", "compiler-v1", "riscv64", "4.33.0", sha256_text("mathlib"), [],
    sha256_text("tactics"), sha256_text("trust"), "verified")
expect(duplicated.verified_identity_diagnostic()).to_contain("DEPENDENCY-HASH")
val blank_solver = VerificationCacheKeyV1(sha256_text("vir"), sha256_text("contract"),
    sha256_text("weave"), sha256_text("macro"), [], "effects-v1", "compiler-v1",
    "riscv64", "4.33.0", sha256_text("mathlib"), [""], sha256_text("tactics"),
    sha256_text("trust"), "verified")
expect(blank_solver.verified_identity_diagnostic()).to_contain("CACHE-SOLVERS")
val key = verified_cache_key()
val closed = TrustManifestV1(["propext"], [], [], [], [], [])
val certificate = valid_compiler_certificate()
val artifact = sha256_text("artifact")
val replay = valid_replay_closure(artifact)
val malformed = ProofReceiptV1("Simple.safe", FormalStatus.ArtifactVerified,
    key.hash(), artifact, [], sha256_text("axioms"), sha256_text(closed.canonical_text()),
    certificate.expected_certificate_hash(), "UPPERCASE")
expect(malformed.verified_identity_diagnostic()).to_contain("REPLAY-HASH")
expect(permits_closed_verified_release(
    ResolvedAssurancePolicyV2(AssuranceStrictnessV2.Verified,
        "nogc_async_mut_noalloc", AssuranceGrade.NoGrade, AssuranceConvention.NoConvention),
    key, malformed, closed, certificate, replay)).to_equal(false)
```

</details>

#### rejects malformed or duplicated theorem dependency identities in an artifact receipt

- rejects malformed or duplicated theorem dependency identities in an artifact receipt


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects malformed or duplicated theorem dependency identities in an artifact receipt")
val key = verified_cache_key()
val closed = TrustManifestV1(["propext"], [], [], [], [], [])
val certificate = valid_compiler_certificate()
val artifact = sha256_text("artifact")
val replay = valid_replay_closure(artifact)
val malformed = ProofReceiptV1("Simple.safe", FormalStatus.ArtifactVerified,
    key.hash(), artifact, ["not-a-hash"], sha256_text("axioms"),
    sha256_text(closed.canonical_text()), certificate.expected_certificate_hash(), replay.hash())
expect(malformed.verified_identity_diagnostic()).to_contain("DEPENDENCY-HASH")
val dependency = sha256_text("theorem-dependency")
val duplicated = ProofReceiptV1("Simple.safe", FormalStatus.ArtifactVerified,
    key.hash(), artifact, [dependency, dependency], sha256_text("axioms"),
    sha256_text(closed.canonical_text()), certificate.expected_certificate_hash(), replay.hash())
expect(duplicated.verified_identity_diagnostic()).to_contain("DEPENDENCY-HASH")
```

</details>

#### rejects blank or duplicated trust declarations rather than normalizing them

- rejects blank or duplicated trust declarations rather than normalizing them
   - Expected: TrustManifestV1(["propext", "propext"], [], [], [], [], []).is_closed() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects blank or duplicated trust declarations rather than normalizing them")
expect(TrustManifestV1(["propext", "propext"], [], [], [], [], []).is_closed()).to_equal(false)
expect(TrustManifestV1([], [], [""], [], [], []).diagnostic()).to_contain("OPERATIONS")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/assurance/formal_receipt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Formal Verification 2.0 evidence receipts.
- Formal Verification 2.0 evidence receipts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `d27165c05261e2557f0394bbdf5afc5b2bb807d7a1d66bd67afbc9eba06a469f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d27165c05261e2557f0394bbdf5afc5b2bb807d7a1d66bd67afbc9eba06a469f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d27165c05261e2557f0394bbdf5afc5b2bb807d7a1d66bd67afbc9eba06a469f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/assurance/formal_receipt_spec.spl
mirror: doc/06_spec/01_unit/compiler/assurance/formal_receipt_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/assurance/formal_receipt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/assurance/formal_receipt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/assurance/formal_receipt_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'canonicalizes unordered cache inputs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/assurance/formal_receipt_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'invalidates a verified cache identity when a semantic dimension changes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/assurance/formal_receipt_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not release an artifact without compiler and replay evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
