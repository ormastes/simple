# SOSIX typed completion and wait-set contract

This unit contract covers REQ-SQ-002 and REQ-SQ-015 for the canonical
asynchronous operation core.

It verifies that:

- terminal operation slots become typed completions without losing partial
  progress;
- decoding a completion as another API is rejected;
- the bounded FIFO rejects overflow without overwriting unread data;
- only a watched `(slot, generation)` may publish a notification;
- duplicate notifications are suppressed; and
- consuming a completion removes its watch so the bounded wait set is reusable.

The state machine contains no sleep, polling loop, environment access, or
process execution. Platform adapters are responsible for signaling and waiting
through their native notification primitive.

REQ-SQ-002/015: typed completion queue and notification wait-set state.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/sosix/completion_wait_set_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

REQ-SQ-002/015: typed completion queue and notification wait-set state.

## Scenarios

### SOSIX typed completion and notification wait set

#### preserves FIFO completion identity and partial progress

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SQ-002/015
```

</details>

#### rejects overflow without overwriting an unread completion

- rejects overflow without overwriting an unread completion
   - Expected: queue.rejected_count() equals `1`
   - Expected: completion.operation.slot equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects overflow without overwriting an unread completion")
val queue = SosixCompletionQueue.create(1)
val first = completed_read(8, sosix_operation_slot_new())
val second = completed_read(9, sosix_operation_slot_new())
expect(queue.publish(first)).to_be(true)
expect(queue.publish(second)).to_be(false)
expect(queue.rejected_count()).to_equal(1)
if val completion = queue.take():
    expect(completion.operation.slot).to_equal(8)
```

</details>

#### prevents completion type confusion

- prevents completion type confusion
   - Expected: decoded.reason equals `completion-api-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("prevents completion type confusion")
val completion = completed_read(5, sosix_operation_slot_new())
val decoded = sosix_completion_expect_api(completion, 0x0102)
expect(decoded.accepted).to_be(false)
expect(decoded.reason).to_equal("completion-api-mismatch")
```

</details>

#### publishes one consumable notification for a watched generation

- publishes one consumable notification for a watched generation
   - Expected: wait_set.notification_generation equals `1`
   - Expected: ready.operation.slot equals `11`
   - Expected: wait_set.consumed_notifications equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("publishes one consumable notification for a watched generation")
val completion = completed_read(11, sosix_operation_slot_new())
val wait_set = SosixWaitSet.create()
expect(wait_set.watch(completion.operation)).to_be(true)
expect(wait_set.notify(completion)).to_be(true)
expect(wait_set.notify(completion)).to_be(false)
expect(wait_set.has_ready()).to_be(true)
expect(wait_set.notification_generation).to_equal(1)

if val ready = wait_set.take_ready():
    expect(ready.operation.slot).to_equal(11)
expect(wait_set.has_ready()).to_be(false)
expect(wait_set.consumed_notifications).to_equal(1)
expect(wait_set.watch(completion.operation)).to_be(true)
expect(wait_set.notify(completion)).to_be(false)
```

</details>

#### rejects an unwatched or stale-generation notification

- rejects an unwatched or stale-generation notification
   - Expected: wait_set.ready_count() equals `0`
   - Expected: wait_set.rejected_notifications equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects an unwatched or stale-generation notification")
val completion = completed_read(15, sosix_operation_slot_new())
val wait_set = SosixWaitSet.create()
val stale = SosixOperationId(slot: 15, generation: completion.operation.generation + 1)
expect(wait_set.watch(stale)).to_be(true)
expect(wait_set.notify(completion)).to_be(false)
expect(wait_set.ready_count()).to_equal(0)
expect(wait_set.rejected_notifications).to_equal(1)
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

- `REQ-SSPEC-OS`
- `REQ-SQ-002/015`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `62b41202664cb31aea87c7c07eb0779c551bd821f0a6db98c851d23ca296ea9d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `62b41202664cb31aea87c7c07eb0779c551bd821f0a6db98c851d23ca296ea9d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `62b41202664cb31aea87c7c07eb0779c551bd821f0a6db98c851d23ca296ea9d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/01_unit/os/sosix/completion_wait_set_spec.spl
mirror: doc/06_spec/01_unit/os/sosix/completion_wait_set_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/sosix/completion_wait_set_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/sosix/completion_wait_set_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/sosix/completion_wait_set_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/sosix/completion_wait_set_spec.spl:24:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'preserves FIFO completion identity and partial progress' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/sosix/completion_wait_set_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects overflow without overwriting an unread completion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/sosix/completion_wait_set_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prevents completion type confusion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/sosix/completion_wait_set_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes one consumable notification for a watched generation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
