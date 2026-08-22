# completion_wait_set_spec

> REQ-SQ-002/015: typed completion queue and notification wait-set state.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# completion_wait_set_spec

REQ-SQ-002/015: typed completion queue and notification wait-set state.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/sosix/completion_wait_set_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

REQ-SQ-002/015: typed completion queue and notification wait-set state.

## Scenarios

### SOSIX typed completion and notification wait set

#### preserves FIFO completion identity and partial progress

- Verify: preserves FIFO completion identity and partial progress
   - Expected: completion.operation.slot equals `3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: queue.len() equals `1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SQ-002/015
# @req: REQ-SQ-002 / REQ-015
# @req: REQ-SQ-002
step("Verify: preserves FIFO completion identity and partial progress")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val queue = SosixCompletionQueue.create(2)
val first = completed_read(3, sosix_operation_slot_new())
val second = completed_read(4, sosix_operation_slot_new())
expect(queue.publish(first)).to_be(true)
expect(queue.publish(second)).to_be(true)

val taken = queue.take()
expect(taken != nil).to_be(true)
if val completion = taken:
    expect(completion.operation.slot).to_equal(3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
    expect(completion.partial_progress).to_be(true)
expect(queue.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### rejects overflow without overwriting an unread completion

- Verify: rejects overflow without overwriting an unread completion
   - Expected: queue.rejected_count() equals `1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: completion.operation.slot equals `8)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SQ-002/015
# @req: REQ-SQ-002 / REQ-015
# @req: REQ-SQ-002
step("Verify: rejects overflow without overwriting an unread completion")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val queue = SosixCompletionQueue.create(1)
val first = completed_read(8, sosix_operation_slot_new())
val second = completed_read(9, sosix_operation_slot_new())
expect(queue.publish(first)).to_be(true)
expect(queue.publish(second)).to_be(false)
expect(queue.rejected_count()).to_equal(1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
if val completion = queue.take():
    expect(completion.operation.slot).to_equal(8)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### prevents completion type confusion

- Verify: prevents completion type confusion
   - Expected: decoded.reason equals `completion-api-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SQ-002/015
# @req: REQ-SQ-002 / REQ-015
# @req: REQ-SQ-002
step("Verify: prevents completion type confusion")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val completion = completed_read(5, sosix_operation_slot_new())
val decoded = sosix_completion_expect_api(completion, 0x0102)
expect(decoded.accepted).to_be(false)
expect(decoded.reason).to_equal("completion-api-mismatch")
```

</details>

#### publishes one consumable notification for a watched generation

- Verify: publishes one consumable notification for a watched generation
   - Expected: wait_set.notification_generation equals `1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: ready.operation.slot equals `11)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`
   - Expected: wait_set.consumed_notifications equals `1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SQ-002/015
# @req: REQ-SQ-002 / REQ-015
# @req: REQ-SQ-002
step("Verify: publishes one consumable notification for a watched generation")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val completion = completed_read(11, sosix_operation_slot_new())
val wait_set = SosixWaitSet.create()
expect(wait_set.watch(completion.operation)).to_be(true)
expect(wait_set.notify(completion)).to_be(true)
expect(wait_set.notify(completion)).to_be(false)
expect(wait_set.has_ready()).to_be(true)
expect(wait_set.notification_generation).to_equal(1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario

if val ready = wait_set.take_ready():
    expect(ready.operation.slot).to_equal(11)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(wait_set.has_ready()).to_be(false)
expect(wait_set.consumed_notifications).to_equal(1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(wait_set.watch(completion.operation)).to_be(true)
expect(wait_set.notify(completion)).to_be(false)
```

</details>

#### rejects an unwatched or stale-generation notification

- Verify: rejects an unwatched or stale-generation notification
   - Expected: wait_set.ready_count() equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: wait_set.rejected_notifications equals `1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SQ-002/015
# @req: REQ-SQ-002 / REQ-015
# @req: REQ-SQ-002
step("Verify: rejects an unwatched or stale-generation notification")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val completion = completed_read(15, sosix_operation_slot_new())
val wait_set = SosixWaitSet.create()
val stale = SosixOperationId(slot: 15, generation: completion.operation.generation + 1)
expect(wait_set.watch(stale)).to_be(true)
expect(wait_set.notify(completion)).to_be(false)
expect(wait_set.ready_count()).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(wait_set.rejected_notifications).to_equal(1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2daa56f69f7be5fca451e4e7d551f60c8dbda7a2d2e5dddd7dc8ebd72b6e7065`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2daa56f69f7be5fca451e4e7d551f60c8dbda7a2d2e5dddd7dc8ebd72b6e7065`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2daa56f69f7be5fca451e4e7d551f60c8dbda7a2d2e5dddd7dc8ebd72b6e7065`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/sosix/completion_wait_set_spec.spl
mirror: doc/06_spec/01_unit/os/sosix/completion_wait_set_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/sosix/completion_wait_set_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/sosix/completion_wait_set_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/sosix/completion_wait_set_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, traceability, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
