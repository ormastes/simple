# Parent Commit Inbox Specification

> Tests covering ParentCommitFrameInboxV1 bounded process ingress.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parent Commit Inbox Specification

## Scenarios

### ParentCommitFrameInboxV1 bounded process ingress

#### binds admission to one child generation and rejects replay

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- binds admission to one child generation and rejects replay


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binds admission to one child generation and rejects replay")
val inbox = parent_commit_frame_inbox_v1_for_generation(2, 41)
val accepted = child_process_result_frame_for_generation(7, 707, 41)
assert_false(inbox.offer_process_result_frame(
    child_process_result_frame_for_generation(8, 708, 40)))
assert_true(inbox.offer_process_result_frame(accepted))
assert_false(inbox.offer_process_result_frame(accepted))
assert_equal(inbox.depth(), 1)
assert_equal(inbox.stats().rejected_session_frames, 1)
assert_equal(inbox.stats().rejected_replay_frames, 1)
```

</details>

#### enforces bounded acceptance and FIFO delivery

- enforces bounded acceptance and FIFO delivery


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enforces bounded acceptance and FIFO delivery")
val inbox = parent_commit_frame_inbox_v1(2)
val first = child_process_result_frame(1, 101)
val second = child_process_result_frame(2, 102)
val third = child_process_result_frame(3, 103)
assert_true(inbox.offer_process_result_frame(first))
assert_true(inbox.offer_process_result_frame(second))
assert_false(inbox.offer_process_result_frame(third))
assert_equal(inbox.depth(), 2)
assert_equal(inbox.stats().high_water_frames, 2)
val received_first = inbox.receive()
assert_true(received_first.ok)
assert_equal(received_first.frame, first)
assert_true(inbox.offer_process_result_frame(third))
val received_second = inbox.receive()
val received_third = inbox.receive()
assert_equal(received_second.frame, second)
assert_equal(received_third.frame, third)
assert_equal(inbox.depth(), 0)
assert_equal(inbox.stats().accepted_frames, 3)
assert_equal(inbox.stats().rejected_frames, 1)
```

</details>

#### retains an isolated copy when the offered frame is later mutated

- retains an isolated copy when the offered frame is later mutated


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retains an isolated copy when the offered frame is later mutated")
val inbox = parent_commit_frame_inbox_v1(1)
var offered = child_process_result_frame(1, 101)
val expected = child_process_result_frame(1, 101)
assert_true(inbox.offer_process_result_frame(offered))
offered[0] = 0
val received = inbox.receive()
assert_true(received.ok)
assert_equal(received.frame, expected)
```

</details>

#### bounds retained bytes independently of frame-count capacity

- bounds retained bytes independently of frame-count capacity


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bounds retained bytes independently of frame-count capacity")
val first = child_process_result_frame(1, 101)
val second = child_process_result_frame(2, 102)
val inbox = parent_commit_frame_inbox_v1_with_byte_budget(2, first.len())
assert_true(inbox.offer_process_result_frame(first))
assert_equal(inbox.retained_byte_count(), first.len())
assert_false(inbox.offer_process_result_frame(second))
assert_equal(inbox.stats().high_water_bytes, first.len())
val received = inbox.receive()
assert_true(received.ok)
assert_equal(inbox.retained_byte_count(), 0)
assert_true(inbox.offer_process_result_frame(second))
```

</details>

#### rejects malformed frames and drains after close

- rejects malformed frames and drains after close


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects malformed frames and drains after close")
val inbox = parent_commit_frame_inbox_v1(1)
assert_false(inbox.offer_process_result_frame([0, 1, 2]))
val valid = child_process_result_frame(1, 101)
assert_true(inbox.offer_process_result_frame(valid))
inbox.close()
assert_true(inbox.is_closed())
assert_false(inbox.offer_process_result_frame(child_process_result_frame(2, 102)))
assert_true(inbox.receive().ok)
assert_equal(inbox.receive().reason, "closed")
```

</details>

#### revokes accepted frames on cancellation without resurrection

- revokes accepted frames on cancellation without resurrection


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("revokes accepted frames on cancellation without resurrection")
val inbox = parent_commit_frame_inbox_v1(2)
assert_true(inbox.offer_process_result_frame(
    child_process_result_frame(1, 101)))
assert_equal(inbox.depth(), 1)
inbox.revoke()
assert_equal(inbox.depth(), 0)
assert_equal(inbox.retained_byte_count(), 0)
assert_equal(inbox.receive().reason, "closed")
assert_false(inbox.offer_process_result_frame(
    child_process_result_frame(2, 102)))
```

</details>

#### drains one accepted frame into the serialized parent root

- drains one accepted frame into the serialized parent root


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("drains one accepted frame into the serialized parent root")
val inbox = parent_commit_frame_inbox_v1(1)
val owner = parent_commit_owner_v1(
    parallel_commit_state_v1(4, 400),
    ParallelCommitOrder.TaskIdThenSequence,
    ParallelConflictPolicy.Reject)
assert_true(inbox.offer_process_result_frame(
    child_process_result_frame(7, 707)))
val committed = owner.commit_next_process_result(inbox, 401)
assert_true(committed.receipt.ok)
assert_equal(committed.receipt.ordered_payload_tokens[0], 707)
assert_equal(inbox.depth(), 0)
assert_equal(owner.commit_next_process_result(inbox, 402).receipt.reason,
    "process-result-inbox-empty")
```

</details>

#### commits a bounded reverse-arrival inbox batch deterministically

- commits a bounded reverse-arrival inbox batch deterministically


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("commits a bounded reverse-arrival inbox batch deterministically")
val inbox = parent_commit_frame_inbox_v1(3)
val owner = parent_commit_owner_v1(
    parallel_commit_state_v1(4, 400),
    ParallelCommitOrder.TaskIdThenSequence,
    ParallelConflictPolicy.Reject)
assert_true(inbox.offer_process_result_frame(
    child_process_result_frame(9, 709)))
assert_true(inbox.offer_process_result_frame(
    child_process_result_frame(2, 702)))
val committed = owner.drain_process_result_batch(inbox, 2, 401)
assert_true(committed.receipt.ok)
assert_equal(committed.receipt.ordered_task_ids[0], 2)
assert_equal(committed.receipt.ordered_payload_tokens[1], 709)
assert_equal(inbox.depth(), 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/parent_commit_inbox_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ParentCommitFrameInboxV1 bounded process ingress.
- ParentCommitFrameInboxV1 bounded process ingress

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `84ed3f1e4013fae47ba708d65f233ae9bcc89ac5b211456c1fa363ee35fd08dd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `84ed3f1e4013fae47ba708d65f233ae9bcc89ac5b211456c1fa363ee35fd08dd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `84ed3f1e4013fae47ba708d65f233ae9bcc89ac5b211456c1fa363ee35fd08dd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_async_mut/parent_commit_inbox_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/parent_commit_inbox_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/parent_commit_inbox_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/parent_commit_inbox_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/parent_commit_inbox_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds admission to one child generation and rejects replay' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/parent_commit_inbox_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'enforces bounded acceptance and FIFO delivery' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/parent_commit_inbox_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retains an isolated copy when the offered frame is later mutated' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
