# DBD retryable close ownership

> Injects close return codes at the ownership commit seam. A failed close keeps

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DBD retryable close ownership

Injects close return codes at the ownership commit seam. A failed close keeps

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/dbd/dbd_close_owner_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Injects close return codes at the ownership commit seam. A failed close keeps
the exact descriptor owned; retries are bounded; quarantine survives restart.

## Scenarios

### DBD listener close failure ownership

#### retains the only descriptor until a retry verifies close

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- retains the only descriptor until a retry verifies close
   - Expected: failed equals `DbdCloseDispositionV1.Retryable`
   - Expected: owner.fd equals `41i64`
   - Expected: owner.state equals `DbdCloseStateV1.CloseRetryable`
   - Expected: owner.close_attempts equals `1i64`
   - Expected: retried equals `DbdCloseDispositionV1.Closed`
   - Expected: owner.fd equals `-1i64`
   - Expected: owner.state equals `DbdCloseStateV1.Closed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retains the only descriptor until a retry verifies close")
var owner = DbdCloseOwnerV1.new("listener")
expect(owner.acquire(41)).to_be(true)
val failed = owner.commit_close_result(-5)
expect(failed).to_equal(DbdCloseDispositionV1.Retryable)
expect(owner.fd).to_equal(41i64)
expect(owner.state).to_equal(DbdCloseStateV1.CloseRetryable)
expect(owner.close_attempts).to_equal(1i64)
expect(owner.owns_fd()).to_be(true)
expect(owner.can_attempt_close()).to_be(true)

val retried = owner.commit_close_result(0)
expect(retried).to_equal(DbdCloseDispositionV1.Closed)
expect(owner.fd).to_equal(-1i64)
expect(owner.state).to_equal(DbdCloseStateV1.Closed)
expect(owner.owns_fd()).to_be(false)
```

</details>

#### does not accept a replacement while close remains retryable

- does not accept a replacement while close remains retryable
   - Expected: owner.fd equals `42i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not accept a replacement while close remains retryable")
var owner = DbdCloseOwnerV1.new("listener")
expect(owner.acquire(42)).to_be(true)
expect(owner.commit_close_result(-1)).to_equal(
    DbdCloseDispositionV1.Retryable)
expect(owner.acquire(43)).to_be(false)
expect(owner.fd).to_equal(42i64)
```

</details>

### DBD client close quarantine

#### bounds retries and preserves the client fd in terminal quarantine

- bounds retries and preserves the client fd in terminal quarantine
   - Expected: disposition equals `DbdCloseDispositionV1.Retryable`
   - Expected: disposition equals `DbdCloseDispositionV1.Quarantined`
   - Expected: owner.state equals `DbdCloseStateV1.Quarantined`
   - Expected: owner.fd equals `71i64`
   - Expected: owner.close_attempts equals `DBD_MAX_CLOSE_ATTEMPTS_V1`
   - Expected: owner.fd equals `71i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bounds retries and preserves the client fd in terminal quarantine")
var owner = DbdCloseOwnerV1.new("client")
expect(owner.acquire(71)).to_be(true)
var attempt: i64 = 0
while attempt < DBD_MAX_CLOSE_ATTEMPTS_V1:
    val disposition = owner.commit_close_result(-9)
    if attempt + 1 < DBD_MAX_CLOSE_ATTEMPTS_V1:
        expect(disposition).to_equal(DbdCloseDispositionV1.Retryable)
    else:
        expect(disposition).to_equal(DbdCloseDispositionV1.Quarantined)
    attempt = attempt + 1
expect(owner.state).to_equal(DbdCloseStateV1.Quarantined)
expect(owner.fd).to_equal(71i64)
expect(owner.owns_fd()).to_be(true)
expect(owner.can_attempt_close()).to_be(false)
expect(owner.commit_close_result(0)).to_equal(
    DbdCloseDispositionV1.Quarantined)
expect(owner.close_attempts).to_equal(DBD_MAX_CLOSE_ATTEMPTS_V1)
expect(owner.fd).to_equal(71i64)
```

</details>

#### carries quarantined ownership across restart without state reset

- carries quarantined ownership across restart without state reset
   - Expected: owner.generation equals `previous_generation + 1`
   - Expected: owner.state equals `DbdCloseStateV1.Quarantined`
   - Expected: owner.fd equals `72i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("carries quarantined ownership across restart without state reset")
var owner = DbdCloseOwnerV1.new("client")
expect(owner.acquire(72)).to_be(true)
var attempt: i64 = 0
while attempt < DBD_MAX_CLOSE_ATTEMPTS_V1:
    val _ = owner.commit_close_result(-1)
    attempt = attempt + 1
val previous_generation = owner.generation
expect(owner.carry_restart()).to_be(true)
expect(owner.generation).to_equal(previous_generation + 1)
expect(owner.state).to_equal(DbdCloseStateV1.Quarantined)
expect(owner.fd).to_equal(72i64)
expect(owner.last_error).to_equal(
    "client-close-quarantined-across-restart")
```

</details>

### DBD closed resource restart

#### reopens acquisition only after verified close and restart

- reopens acquisition only after verified close and restart
   - Expected: owner.generation equals `previous_generation + 1`
   - Expected: owner.state equals `DbdCloseStateV1.Available`
   - Expected: owner.close_attempts equals `0i64`
   - Expected: owner.fd equals `82i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reopens acquisition only after verified close and restart")
var owner = DbdCloseOwnerV1.new("listener")
expect(owner.acquire(81)).to_be(true)
expect(owner.commit_close_result(0)).to_equal(
    DbdCloseDispositionV1.Closed)
val previous_generation = owner.generation
expect(owner.carry_restart()).to_be(true)
expect(owner.generation).to_equal(previous_generation + 1)
expect(owner.state).to_equal(DbdCloseStateV1.Available)
expect(owner.close_attempts).to_equal(0i64)
expect(owner.acquire(82)).to_be(true)
expect(owner.fd).to_equal(82i64)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `ccd64241e618f6f4728f9ed61fb526c8129a596937d23ad07ddee926e3797ba6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ccd64241e618f6f4728f9ed61fb526c8129a596937d23ad07ddee926e3797ba6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ccd64241e618f6f4728f9ed61fb526c8129a596937d23ad07ddee926e3797ba6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/apps/dbd/dbd_close_owner_spec.spl
mirror: doc/06_spec/01_unit/os/apps/dbd/dbd_close_owner_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/apps/dbd/dbd_close_owner_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/apps/dbd/dbd_close_owner_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/apps/dbd/dbd_close_owner_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retains the only descriptor until a retry verifies close' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/dbd/dbd_close_owner_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not accept a replacement while close remains retryable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/dbd/dbd_close_owner_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bounds retries and preserves the client fd in terminal quarantine' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
