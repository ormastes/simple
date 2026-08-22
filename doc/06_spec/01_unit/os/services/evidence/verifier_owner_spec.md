# verifier_owner_spec

> Verifies the verifier owner behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# verifier_owner_spec

Verifies the verifier owner behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/evidence/verifier_owner_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the verifier owner behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### SimpleOS mutex-serialized evidence owner

#### validates roots and linearizes first initialization

- Verify: validates roots and linearizes first initialization


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001
step("Verify: validates roots and linearizes first initialization")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val empty = simpleos_evidence_trust_roots_check([])
expect(empty.ok).to_be(false)
val duplicate = simpleos_evidence_trust_roots_check([
    SimpleOsTrustedEvidenceSignerV1(
        key_id: "same", public_key: [0u8; 32]),
    SimpleOsTrustedEvidenceSignerV1(
        key_id: "same", public_key: [1u8; 32])
])
expect(duplicate.ok).to_be(false)
var too_many: [SimpleOsTrustedEvidenceSignerV1] = []
var root_index: i64 = 0
while root_index < 17:
    too_many = too_many.push(SimpleOsTrustedEvidenceSignerV1(
        key_id: "root-" + root_index.to_text(),
        public_key: [7u8; 32]))
    root_index = root_index + 1
expect(simpleos_evidence_trust_roots_check(too_many).ok).to_be(false)
val first = simpleos_evidence_verifier_start(evidence_owner_roots())
val repeated = simpleos_evidence_verifier_start(evidence_owner_roots())
expect(first.ok).to_be(true)
expect(repeated.ok).to_be(true)
expect(simpleos_evidence_verifier_ready()).to_be(true)
expect(simpleos_evidence_pass_admission_available()).to_be(false)
```

</details>

#### rejects the losing conflicting initializer without replacing roots

- Verify: rejects the losing conflicting initializer without replacing roots
   - Expected: rejected.reason equals `trust-root-already-initialized`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001
step("Verify: rejects the losing conflicting initializer without replacing roots")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: linearizes competing nonce issuance to one accepted generation
   - Expected: losing_call.reason equals `nonce-replay`
   - Expected: invalid_time.reason equals `challenge-time`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001
step("Verify: linearizes competing nonce issuance to one accepted generation")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: retains nonce history after expiry while reusing its bounded slot
   - Expected: replay.reason equals `nonce-replay`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001
step("Verify: retains nonce history after expiry while reusing its bounded slot")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: rejects copied generations and keeps crypto PASS disabled
   - Expected: forged.reason equals `challenge-unknown`
   - Expected: real.reason equals `artifact-rehash-required`
   - Expected: real.handle.handle_id equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001
step("Verify: rejects copied generations and keeps crypto PASS disabled")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: caller-constructed handles cannot consume or advertise authority
   - Expected: first.reason equals `verified-handle-unknown`
   - Expected: second.reason equals `first.reason`
   - Expected: after.ledger.revision equals `before.ledger.revision`
   - Expected: after.ledger.rows.len() equals `before.ledger.rows.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001
step("Verify: caller-constructed handles cannot consume or advertise authority")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: enforces the live challenge bound and deterministically reuses expiry
   - Expected: bounded.reason equals `challenge-bound`
   - Expected: reused.challenge.session_id equals `1u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001
step("Verify: enforces the live challenge bound and deterministically reuses expiry")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2878d2107103bbabcedb81c36f6d0f6b03f7b38eab9545d824a4a11cb2d34d38`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2878d2107103bbabcedb81c36f6d0f6b03f7b38eab9545d824a4a11cb2d34d38`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2878d2107103bbabcedb81c36f6d0f6b03f7b38eab9545d824a4a11cb2d34d38`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/services/evidence/verifier_owner_spec.spl
mirror: doc/06_spec/01_unit/os/services/evidence/verifier_owner_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/services/evidence/verifier_owner_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/services/evidence/verifier_owner_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/evidence/verifier_owner_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
