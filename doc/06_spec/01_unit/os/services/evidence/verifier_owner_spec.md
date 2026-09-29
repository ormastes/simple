# Verifier Owner Specification

> Tests covering SimpleOS mutex-serialized evidence owner.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Verifier Owner Specification

## Scenarios

### SimpleOS mutex-serialized evidence owner

#### validates roots and linearizes first initialization

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-001
```

</details>

#### rejects the losing conflicting initializer without replacing roots

- rejects the losing conflicting initializer without replacing roots
   - Expected: rejected.reason equals `trust-root-already-initialized`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects the losing conflicting initializer without replacing roots")
expect(simpleos_evidence_verifier_start(
    evidence_owner_roots()).ok).to_be(true)
var conflicting = evidence_owner_roots()
var changed = conflicting[0]
changed.key_id = "other-root"
conflicting[0] = changed
val rejected = simpleos_evidence_verifier_start(conflicting)
expect(rejected.ok).to_be(false)
expect(rejected.reason).to_equal("trust-root-already-initialized")
expect(simpleos_evidence_verifier_start(
    evidence_owner_roots()).ok).to_be(true)
expect(simpleos_evidence_verifier_ready()).to_be(true)
```

</details>

#### linearizes competing nonce issuance to one accepted generation

- linearizes competing nonce issuance to one accepted generation
   - Expected: losing_call.reason equals `nonce-replay`
   - Expected: invalid_time.reason equals `challenge-time`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("linearizes competing nonce issuance to one accepted generation")
# This is the deterministic owner model for either mutex acquisition
# order: whichever contender enters first succeeds, the other observes
# the committed nonce and loses without a second generation.
expect(simpleos_evidence_verifier_start(
    evidence_owner_roots()).ok).to_be(true)
val first = simpleos_evidence_issue_challenge(
    "nonce-concurrent", 100, 10)
val losing_call = simpleos_evidence_issue_challenge(
    "nonce-concurrent", 100, 10)
expect(first.ok).to_be(true)
expect(first.challenge.session_id).to_be_greater_than(0u64)
expect(first.challenge.generation).to_be_greater_than(0u64)
expect(losing_call.ok).to_be(false)
expect(losing_call.reason).to_equal("nonce-replay")
val invalid_time = simpleos_evidence_issue_challenge(
    "nonce-time", 100, SIMPLEOS_EVIDENCE_MAX_CHALLENGE_TTL_US + 1)
expect(invalid_time.ok).to_be(false)
expect(invalid_time.reason).to_equal("challenge-time")
```

</details>

#### retains nonce history after expiry while reusing its bounded slot

- retains nonce history after expiry while reusing its bounded slot
   - Expected: replay.reason equals `nonce-replay`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("retains nonce history after expiry while reusing its bounded slot")
expect(simpleos_evidence_verifier_start(
    evidence_owner_roots()).ok).to_be(true)
val first = simpleos_evidence_issue_challenge(
    "nonce-expired", 1000, 10)
expect(first.ok).to_be(true)
val replacement = simpleos_evidence_issue_challenge(
    "nonce-replacement", 1011, 10)
expect(replacement.ok).to_be(true)
expect(replacement.challenge.session_id).to_equal(
    first.challenge.session_id)
expect(replacement.challenge.generation).to_be_greater_than(
    first.challenge.generation)
val replay = simpleos_evidence_issue_challenge(
    "nonce-expired", 1022, 10)
expect(replay.ok).to_be(false)
expect(replay.reason).to_equal("nonce-replay")
```

</details>

#### rejects copied generations and keeps crypto PASS disabled

- rejects copied generations and keeps crypto PASS disabled
   - Expected: forged.reason equals `challenge-unknown`
   - Expected: real.reason equals `artifact-rehash-required`
   - Expected: real.handle.handle_id equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects copied generations and keeps crypto PASS disabled")
expect(simpleos_evidence_verifier_start(
    evidence_owner_roots()).ok).to_be(true)
val issued = simpleos_evidence_issue_challenge(
    "nonce-copy", 2000, 100)
expect(issued.ok).to_be(true)
var copied = issued.challenge
copied.generation = 2u64
if copied.generation == issued.challenge.generation:
    copied.generation = copied.generation + 1u64
val candidate = evidence_owner_candidate("nonce-copy")
var fresh_receipt = candidate.receipt
fresh_receipt.started_unix_us = 2010
fresh_receipt.finished_unix_us = 2020
var fresh_candidate = candidate
fresh_candidate.receipt = fresh_receipt
val forged = simpleos_evidence_verify_candidate(
    fresh_candidate, copied, "protocol-inventory", 2030)
expect(forged.ok).to_be(false)
expect(forged.reason).to_equal("challenge-unknown")
val real = simpleos_evidence_verify_candidate(
    fresh_candidate, issued.challenge, "protocol-inventory", 2030)
expect(real.ok).to_be(false)
expect(real.reason).to_equal("artifact-rehash-required")
expect(real.handle.handle_id).to_equal("")
```

</details>

#### caller-constructed handles cannot consume or advertise authority

- caller-constructed handles cannot consume or advertise authority
   - Expected: first.reason equals `verified-handle-unknown`
   - Expected: second.reason equals `first.reason`
   - Expected: after.ledger.revision equals `before.ledger.revision`
   - Expected: after.ledger.rows.len() equals `before.ledger.rows.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("caller-constructed handles cannot consume or advertise authority")
expect(simpleos_evidence_verifier_start(
    evidence_owner_roots()).ok).to_be(true)
val candidate = evidence_owner_candidate("nonce-handle")
val forged = SimpleOsVerifiedEvidenceHandleV1(
    handle_id: "evh-1",
    receipt_id: candidate.receipt.receipt_id,
    receipt_nonce: candidate.receipt.nonce,
    row_key: simpleos_capability_row_key(candidate.row),
    consumer: "protocol-inventory",
    generation: 1u64,
    expires_unix_us: 200)
val before = simpleos_evidence_ledger_snapshot()
val first = simpleos_evidence_consume_verified(
    forged, candidate, "protocol-inventory", 140)
val second = simpleos_evidence_consume_verified(
    forged, candidate, "protocol-inventory", 140)
expect(first.ok).to_be(false)
expect(second.ok).to_be(false)
expect(first.reason).to_equal("verified-handle-unknown")
expect(second.reason).to_equal(first.reason)
val after = simpleos_evidence_ledger_snapshot()
expect(before.ok).to_be(true)
expect(after.ok).to_be(true)
expect(after.ledger.revision).to_equal(before.ledger.revision)
expect(after.ledger.rows.len()).to_equal(before.ledger.rows.len())
expect(after.ledger.consumed_nonces).to_equal(
    before.ledger.consumed_nonces)
expect(simpleos_evidence_row_admitted(
    simpleos_capability_row_key(candidate.row), 140)).to_be(false)
expect(simpleos_evidence_release_verified(
    forged, "protocol-inventory")).to_be(false)
```

</details>

#### enforces the live challenge bound and deterministically reuses expiry

- enforces the live challenge bound and deterministically reuses expiry
   - Expected: bounded.reason equals `challenge-bound`
   - Expected: reused.challenge.session_id equals `1u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("enforces the live challenge bound and deterministically reuses expiry")
expect(simpleos_evidence_verifier_start(
    evidence_owner_roots()).ok).to_be(true)
var i: i64 = 0
while i < 128:
    val issued = simpleos_evidence_issue_challenge(
        "nonce-bound-" + i.to_text(), 10000, 10)
    expect(issued.ok).to_be(true)
    i = i + 1
val bounded = simpleos_evidence_issue_challenge(
    "nonce-bound-overflow", 10000, 10)
expect(bounded.ok).to_be(false)
expect(bounded.reason).to_equal("challenge-bound")
val reused = simpleos_evidence_issue_challenge(
    "nonce-bound-reused", 10011, 10)
expect(reused.ok).to_be(true)
expect(reused.challenge.session_id).to_equal(1u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/evidence/verifier_owner_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS mutex-serialized evidence owner.
- SimpleOS mutex-serialized evidence owner

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
- `REQ-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9c3bac5b1fb1832fcd1d65684b9537442d0a1d9566abec01dd4618beb7b6b1d9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9c3bac5b1fb1832fcd1d65684b9537442d0a1d9566abec01dd4618beb7b6b1d9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9c3bac5b1fb1832fcd1d65684b9537442d0a1d9566abec01dd4618beb7b6b1d9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/os/services/evidence/verifier_owner_spec.spl
mirror: doc/06_spec/01_unit/os/services/evidence/verifier_owner_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/services/evidence/verifier_owner_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/evidence/verifier_owner_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/services/evidence/verifier_owner_spec.spl:128:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'validates roots and linearizes first initialization' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/services/evidence/verifier_owner_spec.spl:157:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects the losing conflicting initializer without replacing roots' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/evidence/verifier_owner_spec.spl:173:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'linearizes competing nonce issuance to one accepted generation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/evidence/verifier_owner_spec.spl:195:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retains nonce history after expiry while reusing its bounded slot' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
