# Parent Commit Owner Specification

> Tests covering ParentCommitOwnerV1 serialized publication.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parent Commit Owner Specification

## Scenarios

### ParentCommitOwnerV1 serialized publication

#### issues unique process generations from the sole parent authority

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- issues unique process generations from the sole parent authority


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("issues unique process generations from the sole parent authority")
val owner = parent_commit_owner_v1(
    parallel_commit_state_v1(1, 100),
    ParallelCommitOrder.TaskIdThenSequence,
    ParallelConflictPolicy.Reject)
val first = owner.issue_process_session_generation()
val second = owner.issue_process_session_generation()
assert_true(first > 0)
assert_equal(second, first + 1)
```

</details>

#### publishes one deterministic child batch and exposes the new root

- publishes one deterministic child batch and exposes the new root


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("publishes one deterministic child batch and exposes the new root")
val owner = parent_commit_owner_v1(
    parallel_commit_state_v1(4, 400),
    ParallelCommitOrder.TaskIdThenSequence,
    ParallelConflictPolicy.Reject)
val late = result_envelope_v1(4, 9, 0, 19,
    ParallelResultKind.Patch, 709, "late")
val early = result_envelope_v1(4, 2, 0, 12,
    ParallelResultKind.Patch, 702, "early")
val outcome = owner.commit([late, early], 401)
assert_true(outcome.receipt.ok)
assert_equal(outcome.receipt.ordered_task_ids[0], 2)
if val snapshot = owner.snapshot():
    assert_equal(snapshot.revision, 5)
    assert_equal(snapshot.snapshot_token, 401)
else:
    assert_false(true)
```

</details>

#### retains the published root when a later child result is stale

- retains the published root when a later child result is stale


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retains the published root when a later child result is stale")
val owner = parent_commit_owner_v1(
    parallel_commit_state_v1(4, 400),
    ParallelCommitOrder.TaskIdThenSequence,
    ParallelConflictPolicy.Reject)
val first = result_envelope_v1(4, 1, 0, 11,
    ParallelResultKind.Patch, 701, "first")
assert_true(owner.commit([first], 401).receipt.ok)
val stale = result_envelope_v1(4, 2, 0, 12,
    ParallelResultKind.Patch, 702, "stale")
val rejected = owner.commit([stale], 402)
assert_false(rejected.receipt.ok)
assert_equal(rejected.receipt.reason, "stale-base-revision")
if val snapshot = owner.snapshot():
    assert_equal(snapshot.revision, 5)
    assert_equal(snapshot.snapshot_token, 401)
else:
    assert_false(true)
```

</details>

#### requires a non-parent child boundary before it commits a result

- requires a non-parent child boundary before it commits a result


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires a non-parent child boundary before it commits a result")
val owner = parent_commit_owner_v1(
    parallel_commit_state_v1(4, 400),
    ParallelCommitOrder.TaskIdThenSequence,
    ParallelConflictPolicy.Reject)
val child_result = result_envelope_v1(4, 7, 0, 17,
    ParallelResultKind.Patch, 707, "child")
val returned = parent_commit_submission_v1(
    transfer_envelope_v1(17, 0,
        ParallelExecutionDomain.Actor,
        ParallelExecutionDomain.Parent,
        ParallelTransferMode.Copy,
        ParallelTransferPayload.InlineCopy,
        0, false),
    child_result)
assert_true(owner.commit_submissions([returned], 401).receipt.ok)
val forged_parent_source = parent_commit_submission_v1(
    transfer_envelope_v1(18, 0,
        ParallelExecutionDomain.Parent,
        ParallelExecutionDomain.Parent,
        ParallelTransferMode.Copy,
        ParallelTransferPayload.InlineCopy,
        0, false),
    result_envelope_v1(5, 8, 0, 18,
        ParallelResultKind.Patch, 708, "forged"))
val rejected = owner.commit_submissions([forged_parent_source], 402)
assert_false(rejected.receipt.ok)
assert_equal(rejected.receipt.reason, "invalid-child-result-transfer")
```

</details>

#### decodes an encoded child-process result before publishing it

- decodes an encoded child-process result before publishing it


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes an encoded child-process result before publishing it")
val owner = parent_commit_owner_v1(
    parallel_commit_state_v1(4, 400),
    ParallelCommitOrder.TaskIdThenSequence,
    ParallelConflictPolicy.Reject)
val result = result_envelope_v1(4, 7, 0, 17,
    ParallelResultKind.Patch, 707, "child")
val envelope = transfer_envelope_v1(17, 0,
    ParallelExecutionDomain.Process,
    ParallelExecutionDomain.Parent,
    ParallelTransferMode.Copy,
    ParallelTransferPayload.EncodedCopy,
    0, false)
val frame = encode_process_transfer_frame(
    process_transfer_frame_v1(envelope, encode_result_envelope(result)))
val committed = owner.commit_process_result_frame(frame, 401)
assert_true(committed.receipt.ok)
assert_equal(committed.receipt.ordered_payload_tokens[0], 707)
```

</details>

#### rejects malformed encoded process result bytes before publication

- rejects malformed encoded process result bytes before publication


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects malformed encoded process result bytes before publication")
val owner = parent_commit_owner_v1(
    parallel_commit_state_v1(4, 400),
    ParallelCommitOrder.TaskIdThenSequence,
    ParallelConflictPolicy.Reject)
val rejected = owner.commit_process_result_frame([0, 1, 2], 401)
assert_false(rejected.receipt.ok)
assert_equal(rejected.receipt.reason, "invalid-process-result-frame")
```

</details>

#### commits a reverse-arrival process batch in canonical task order

- commits a reverse-arrival process batch in canonical task order


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("commits a reverse-arrival process batch in canonical task order")
val owner = parent_commit_owner_v1(
    parallel_commit_state_v1(4, 400),
    ParallelCommitOrder.TaskIdThenSequence,
    ParallelConflictPolicy.Reject)
val late = result_envelope_v1(4, 9, 0, 19,
    ParallelResultKind.Patch, 709, "late")
val early = result_envelope_v1(4, 2, 0, 12,
    ParallelResultKind.Patch, 702, "early")
val late_envelope = transfer_envelope_v1(19, 0,
    ParallelExecutionDomain.Process,
    ParallelExecutionDomain.Parent,
    ParallelTransferMode.Copy,
    ParallelTransferPayload.EncodedCopy,
    0, false)
val early_envelope = transfer_envelope_v1(12, 0,
    ParallelExecutionDomain.Process,
    ParallelExecutionDomain.Parent,
    ParallelTransferMode.Copy,
    ParallelTransferPayload.EncodedCopy,
    0, false)
val committed = owner.commit_process_result_frames([
    encode_process_transfer_frame(process_transfer_frame_v1(
        late_envelope, encode_result_envelope(late))),
    encode_process_transfer_frame(process_transfer_frame_v1(
        early_envelope, encode_result_envelope(early)))
], 401)
assert_true(committed.receipt.ok)
assert_equal(committed.receipt.ordered_task_ids[0], 2)
assert_equal(committed.receipt.ordered_payload_tokens[1], 709)
```

</details>

#### publishes one verified application candidate with a mutation receipt

- publishes one verified application candidate with a mutation receipt


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("publishes one verified application candidate with a mutation receipt")
val owner = parent_commit_owner_v1(
    parallel_commit_state_v1(4, 400),
    ParallelCommitOrder.TaskIdThenSequence,
    ParallelConflictPolicy.Reject)
val late = result_envelope_v1(4, 9, 0, 19,
    ParallelResultKind.Patch, 709, "late")
val early = result_envelope_v1(4, 2, 0, 12,
    ParallelResultKind.Patch, 702, "early")
val late_envelope = transfer_envelope_v1(19, 0,
    ParallelExecutionDomain.Process, ParallelExecutionDomain.Parent,
    ParallelTransferMode.Copy, ParallelTransferPayload.EncodedCopy, 0, false)
val early_envelope = transfer_envelope_v1(12, 0,
    ParallelExecutionDomain.Process, ParallelExecutionDomain.Parent,
    ParallelTransferMode.Copy, ParallelTransferPayload.EncodedCopy, 0, false)
val outcome = owner.commit_process_result_frames_with_candidate([
    encode_process_transfer_frame(process_transfer_frame_v1(
        late_envelope, encode_result_envelope(late))),
    encode_process_transfer_frame(process_transfer_frame_v1(
        early_envelope, encode_result_envelope(early)))
], parent_commit_candidate_v1(401, [702, 709]))
assert_true(outcome.commit.receipt.ok)
assert_true(outcome.mutation.ok)
assert_equal(outcome.mutation.before_revision, 4)
assert_equal(outcome.mutation.after_revision, 5)
assert_equal(outcome.mutation.applied_payload_tokens, [702, 709])
if val payload_root = owner.snapshot_application_payload_root():
    assert_equal(payload_root, [702, 709])
else:
    assert_false(true)
```

</details>

#### rolls back the complete batch when apply verify or one frame fails

- rolls back the complete batch when apply verify or one frame fails


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rolls back the complete batch when apply verify or one frame fails")
val owner = parent_commit_owner_v1_with_application_root(
    parallel_commit_state_v1(4, 400),
    [600],
    ParallelCommitOrder.TaskIdThenSequence,
    ParallelConflictPolicy.Reject)
val result = result_envelope_v1(4, 7, 0, 17,
    ParallelResultKind.Patch, 707, "child")
val envelope = transfer_envelope_v1(17, 0,
    ParallelExecutionDomain.Process, ParallelExecutionDomain.Parent,
    ParallelTransferMode.Copy, ParallelTransferPayload.EncodedCopy, 0, false)
val frame = encode_process_transfer_frame(process_transfer_frame_v1(
    envelope, encode_result_envelope(result)))
val mismatched = owner.commit_process_result_frames_with_candidate(
    [frame], parent_commit_candidate_v1(401, [600, 999]))
assert_equal(mismatched.mutation.reason, "candidate-application-root-mismatch")
val malformed = owner.commit_process_result_frames_with_candidate(
    [frame, [0, 1, 2]], parent_commit_candidate_v1(401, [600, 707]))
assert_equal(malformed.mutation.reason, "invalid-process-result-frame")
val conflicting_result = result_envelope_v1(4, 7, 0, 18,
    ParallelResultKind.Patch, 708, "conflict")
val conflicting_envelope = transfer_envelope_v1(18, 0,
    ParallelExecutionDomain.Process, ParallelExecutionDomain.Parent,
    ParallelTransferMode.Copy, ParallelTransferPayload.EncodedCopy, 0, false)
val conflicting_frame = encode_process_transfer_frame(process_transfer_frame_v1(
    conflicting_envelope, encode_result_envelope(conflicting_result)))
val conflict = owner.commit_process_result_frames_with_candidate(
    [frame, conflicting_frame], parent_commit_candidate_v1(401, [600, 707, 708]))
assert_false(conflict.mutation.ok)
if val snapshot = owner.snapshot():
    assert_equal(snapshot.revision, 4)
    assert_equal(snapshot.snapshot_token, 400)
else:
    assert_false(true)
if val payload_root = owner.snapshot_application_payload_root():
    assert_equal(payload_root, [600])
else:
    assert_false(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/parent_commit_owner_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ParentCommitOwnerV1 serialized publication.
- ParentCommitOwnerV1 serialized publication

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

- Canonical SPipe generation for source `964085f48f430b16511389ac9c1fabe48902e8612210bd3f2054f508067d6ae5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `964085f48f430b16511389ac9c1fabe48902e8612210bd3f2054f508067d6ae5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `964085f48f430b16511389ac9c1fabe48902e8612210bd3f2054f508067d6ae5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_async_mut/parent_commit_owner_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/parent_commit_owner_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/parent_commit_owner_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/parent_commit_owner_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/parent_commit_owner_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'issues unique process generations from the sole parent authority' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/parent_commit_owner_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes one deterministic child batch and exposes the new root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/parent_commit_owner_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retains the published root when a later child result is stale' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
