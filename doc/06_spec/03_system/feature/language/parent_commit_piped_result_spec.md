# Parent-authoritative piped child-result evidence

> This executable system specification exercises the real process-transfer path

<!-- sdn-diagram:id=parent_commit_piped_result_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parent_commit_piped_result_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parent_commit_piped_result_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parent_commit_piped_result_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parent-authoritative piped child-result evidence

This executable system specification exercises the real process-transfer path

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/language/parent_commit_piped_result_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

This executable system specification exercises the real process-transfer path
from a bounded parent-owned session through validation, application-root
verification, and deterministic parent commit. It is written for language and
runtime maintainers reviewing actor/process ownership guarantees.

The primary scenario starts a real child process. The child emits one armored
result in two fragments and then replays the same frame. The parent session
must retain the incomplete suffix, admit the first complete frame, reject the
replay, commit only the admitted frame, and close the native handle at most
once. Supporting scenarios make copied frame retention and atomic rollback
independently observable.

Requirements: REQ-PAR-002, REQ-PAR-003, REQ-PAR-005, REQ-PAR-006,
REQ-PAR-008, REQ-PAR-009, NFR-PAR-001, NFR-PAR-002, NFR-PAR-003.

Run with the admitted pure-Simple runtime:

    SIMPLE_LIB=src bin/release/simple test test/03_system/feature/language/parent_commit_piped_result_spec.spl --mode=native

The Rust bootstrap seed is not acceptance evidence. See the mirrored operator
manual and system-test plan for the current runner/doc-generation boundary.

## Scenarios

### parent-authoritative piped child results

#### should validate, commit, and close one fragmented child result

- should validate, commit, and close one fragmented child result
- Create a bounded parent-owned process session
   - Expected: initial.closed is false
- Receive a fragmented encoded child result
   - Expected: saw_fragment is true
   - Expected: accepted_total equals `1`
   - Expected: inbox.depth() equals `1`
- Reject stale or replayed child output
   - Expected: rejected_total equals `1`
   - Expected: intake_stats.accepted_frames equals `1`
   - Expected: intake_stats.rejected_replay_frames equals `1`
   - Expected: intake_stats.rejected_session_frames equals `0`
- Commit one validated batch at the parent
   - Expected: outcome.commit.receipt.ok is true
   - Expected: outcome.commit.receipt.ordered_task_ids equals `[7]`
   - Expected: outcome.commit.receipt.ordered_payload_tokens equals `[707]`
   - Expected: outcome.mutation.ok is true
   - Expected: outcome.mutation.before_revision equals `4`
   - Expected: outcome.mutation.after_revision equals `5`
   - Expected: outcome.mutation.before_application_payload_root equals `[]`
   - Expected: outcome.mutation.after_application_payload_root equals `[707]`
   - Expected: inbox.depth() equals `0`
   - Expected: snapshot.revision equals `5`
   - Expected: snapshot.snapshot_token equals `401`
   - Expected: application_root equals `[707]`
- Close the child transport exactly once
   - Expected: session.close() is true
   - Expected: session.close() is true
   - Expected: terminal.closed is true
   - Expected: terminal.alive is false
   - Expected: terminal.close_attempts equals `1`
   - Expected: terminal.terminal_reason equals `exited`
   - Expected: terminal.terminal_reason equals `closed`
   - Expected: comparison.status equals `EvidenceStatus.passed`
   - Expected: comparison.summary equals `11 check(s) passed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 132 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PAR-002
# @req REQ-PAR-003
# @req REQ-PAR-005
# @req REQ-PAR-006
# @req REQ-PAR-008
# @req REQ-PAR-009
# @req REQ-PAR-002
# @req REQ-PAR-003
# @req REQ-PAR-005
# @req REQ-PAR-006
# @req REQ-PAR-008
# @req REQ-PAR-009
# @req REQ-SSPEC-SYSTEM
step("should validate, commit, and close one fragmented child result")
step("Create a bounded parent-owned process session")
val owner = parent_commit_owner_v1(
    parallel_commit_state_v1(4, 400),
    ParallelCommitOrder.TaskIdThenSequence,
    ParallelConflictPolicy.Reject)
val generation = owner.issue_process_session_generation()
expect(generation).to_be_greater_than(0)
val inbox = parent_commit_frame_inbox_v1_for_generation(4, generation)
val line = child_result_line(generation)
val session = parent_commit_piped_process_session_v1(
    "/bin/sh",
    ["-c", fragmented_replay_child_script(line)],
    generation,
    inbox)
val initial = session.status()
expect(initial.process_handle).to_be_greater_than(0)
expect(initial.closed).to_equal(false)

step("Receive a fragmented encoded child result")
var accepted_total = 0
var rejected_total = 0
var saw_fragment = false
var polls = 0
while polls < 120:
    if accepted_total >= 1 and rejected_total >= 1 and session.status().closed:
        break
    val read = session.poll(2)
    if accepted_total == 0 and read.pending_bytes > 0:
        saw_fragment = true
    accepted_total = accepted_total + read.accepted
    rejected_total = rejected_total + read.rejected
    polls = polls + 1
    if not session.status().closed:
        thread_sleep(5)
print "fragmented evidence accepted={accepted_total} rejected={rejected_total} depth={inbox.depth()} fragment={saw_fragment} closed={session.status().closed}"
expect(saw_fragment).to_equal(true)
expect(accepted_total).to_equal(1)
expect(inbox.depth()).to_equal(1)
expect(session.reader.pending_high_water_byte_count()).to_be_greater_than(0)

step("Reject stale or replayed child output")
expect(rejected_total).to_equal(1)
val intake_stats = inbox.stats()
expect(intake_stats.accepted_frames).to_equal(1)
expect(intake_stats.rejected_replay_frames).to_equal(1)
expect(intake_stats.rejected_session_frames).to_equal(0)

step("Commit one validated batch at the parent")
val outcome = drain_process_result_batch(owner, inbox, 401, [707])
expect(outcome.commit.receipt.ok).to_equal(true)
expect(outcome.commit.receipt.ordered_task_ids).to_equal([7])
expect(outcome.commit.receipt.ordered_payload_tokens).to_equal([707])
expect(outcome.mutation.ok).to_equal(true)
expect(outcome.mutation.before_revision).to_equal(4)
expect(outcome.mutation.after_revision).to_equal(5)
expect(outcome.mutation.before_application_payload_root).to_equal([])
expect(outcome.mutation.after_application_payload_root).to_equal([707])
expect(inbox.depth()).to_equal(0)
var observed_snapshot_token = -1
if val snapshot = owner.snapshot():
    expect(snapshot.revision).to_equal(5)
    expect(snapshot.snapshot_token).to_equal(401)
    observed_snapshot_token = snapshot.snapshot_token
else:
    fail("committed parent snapshot must remain available")
if val application_root = owner.snapshot_application_payload_root():
    expect(application_root).to_equal([707])
else:
    fail("verified parent application root must remain available")

step("Close the child transport exactly once")
expect(session.close()).to_equal(true)
expect(session.close()).to_equal(true)
val terminal = session.status()
expect(terminal.closed).to_equal(true)
expect(terminal.alive).to_equal(false)
expect(terminal.close_attempts).to_equal(1)
if terminal.naturally_exited:
    expect(terminal.terminal_reason).to_equal("exited")
else:
    expect(terminal.terminal_reason).to_equal("closed")

val evidence = canonical_evidence(
    "protocol",
    "parent-commit-piped-result/v1",
    [
        evidence_node("transport.accepted", "{accepted_total}"),
        evidence_node("transport.rejected", "{rejected_total}"),
        evidence_node("transport.replay_rejected", "{intake_stats.rejected_replay_frames}"),
        evidence_node("commit.receipt_ok", "{outcome.commit.receipt.ok}"),
        evidence_node("commit.mutation_ok", "{outcome.mutation.ok}"),
        evidence_node("commit.before_revision", "{outcome.mutation.before_revision}"),
        evidence_node("commit.after_revision", "{outcome.mutation.after_revision}"),
        evidence_node("commit.snapshot_token", "{observed_snapshot_token}"),
        evidence_node("lifecycle.closed", "{terminal.closed}"),
        evidence_node("lifecycle.alive", "{terminal.alive}"),
        evidence_node("lifecycle.close_attempts", "{terminal.close_attempts}")
    ]
)
val oracle = oracle_spec(
    "parent-commit-piped-result/v1",
    [
        check_exact("transport.accepted", "1"),
        check_exact("transport.rejected", "1"),
        check_exact("transport.replay_rejected", "1"),
        check_exact("commit.receipt_ok", "true"),
        check_exact("commit.mutation_ok", "true"),
        check_exact("commit.before_revision", "4"),
        check_exact("commit.after_revision", "5"),
        check_exact("commit.snapshot_token", "401"),
        check_exact("lifecycle.closed", "true"),
        check_exact("lifecycle.alive", "false"),
        check_exact("lifecycle.close_attempts", "1")
    ]
)
val comparison = compare_evidence(evidence, oracle)
expect(comparison.status).to_equal(EvidenceStatus.passed)
expect(comparison.summary).to_equal("11 check(s) passed")
```

</details>

<details>
<summary>Advanced: should retain an owned copy before the producer mutates its frame</summary>

#### should retain an owned copy before the producer mutates its frame

- should retain an owned copy before the producer mutates its frame
- Offer one encoded frame into parent-owned bounded storage
   - Expected: inbox.offer_process_result_frame(offered) is true
- Mutate the producer buffer and compare the retained parent copy
   - Expected: received.ok is true
   - Expected: received.frame equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain an owned copy before the producer mutates its frame")
step("Offer one encoded frame into parent-owned bounded storage")
val inbox = parent_commit_frame_inbox_v1_for_generation(2, 41)
val expected = child_result_frame(9, 909, 41)
var offered = child_result_frame(9, 909, 41)

expect(inbox.offer_process_result_frame(offered)).to_equal(true)

step("Mutate the producer buffer and compare the retained parent copy")
offered[0] = 0

val received = inbox.receive()
expect(received.ok).to_equal(true)
expect(received.frame).to_equal(expected)
```

</details>


</details>

<details>
<summary>Advanced: should roll back a mixed valid and malformed process batch</summary>

#### should roll back a mixed valid and malformed process batch

- should roll back a mixed valid and malformed process batch
- Submit one valid and one malformed frame as one candidate batch
- Verify both canonical roots remain unchanged after rejection
   - Expected: outcome.commit.receipt.ok is false
   - Expected: outcome.mutation.ok is false
   - Expected: outcome.mutation.reason equals `invalid-process-result-frame`
   - Expected: outcome.mutation.before_revision equals `4`
   - Expected: outcome.mutation.after_revision equals `4`
   - Expected: outcome.mutation.before_application_payload_root equals `[600]`
   - Expected: outcome.mutation.after_application_payload_root equals `[600]`
   - Expected: snapshot.revision equals `4`
   - Expected: snapshot.snapshot_token equals `800`
   - Expected: application_root equals `[600]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should roll back a mixed valid and malformed process batch")
step("Submit one valid and one malformed frame as one candidate batch")
val owner = parent_commit_owner_v1_with_application_root(
    parallel_commit_state_v1(4, 800),
    [600],
    ParallelCommitOrder.TaskIdThenSequence,
    ParallelConflictPolicy.Reject)
val valid = child_result_frame(21, 2100, 51)

val outcome = owner.commit_process_result_frames_with_candidate(
    [valid, [0, 1, 2]], parent_commit_candidate_v1(801, [600, 2100]))

print "rollback evidence ok={outcome.mutation.ok} reason={outcome.mutation.reason} before={outcome.mutation.before_revision} after={outcome.mutation.after_revision}"

step("Verify both canonical roots remain unchanged after rejection")
expect(outcome.commit.receipt.ok).to_equal(false)
expect(outcome.mutation.ok).to_equal(false)
expect(outcome.mutation.reason).to_equal("invalid-process-result-frame")
expect(outcome.mutation.before_revision).to_equal(4)
expect(outcome.mutation.after_revision).to_equal(4)
expect(outcome.mutation.before_application_payload_root).to_equal([600])
expect(outcome.mutation.after_application_payload_root).to_equal([600])
if val snapshot = owner.snapshot():
    expect(snapshot.revision).to_equal(4)
    expect(snapshot.snapshot_token).to_equal(800)
else:
    fail("rejected process batch must preserve the parent snapshot")
if val application_root = owner.snapshot_application_payload_root():
    expect(application_root).to_equal([600])
else:
    fail("rejected process batch must preserve the application root")
```

</details>


</details>

<details>
<summary>Advanced: should cancel a live child and revoke its accepted result</summary>

#### should cancel a live child and revoke its accepted result

- should cancel a live child and revoke its accepted result
- Start a generation-bound child that remains alive after emitting
   - Expected: accepted equals `1`
   - Expected: inbox.depth() equals `1`
- Cancel the child and revoke retained ingress exactly once
   - Expected: session.cancel() is true
   - Expected: session.cancel() is true
   - Expected: terminal.cancelled is true
   - Expected: terminal.closed is true
   - Expected: terminal.alive is false
   - Expected: terminal.close_attempts equals `1`
   - Expected: terminal.terminal_reason equals `cancelled`
   - Expected: inbox.depth() equals `0`
   - Expected: inbox.receive().reason equals `closed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should cancel a live child and revoke its accepted result")
step("Start a generation-bound child that remains alive after emitting")
val lifecycle_owner = parent_commit_owner_v1(
    parallel_commit_state_v1(1, 100),
    ParallelCommitOrder.TaskIdThenSequence,
    ParallelConflictPolicy.Reject)
val generation = lifecycle_owner.issue_process_session_generation()
expect(generation).to_be_greater_than(0)
val inbox = parent_commit_frame_inbox_v1_for_generation(1, generation)
val line = child_result_line(generation)
val session = parent_commit_piped_process_session_v1(
    "/bin/sh", ["-c", "printf '%s\\n' '" + line + "'; sleep 5"],
    generation, inbox)
expect(session.status().process_handle).to_be_greater_than(0)
var accepted = 0
var polls = 0
while polls < 40 and accepted == 0:
    val read = session.poll(1)
    accepted = accepted + read.accepted
    if accepted == 0:
        thread_sleep(5)
    polls = polls + 1
expect(accepted).to_equal(1)
expect(inbox.depth()).to_equal(1)

step("Cancel the child and revoke retained ingress exactly once")
expect(session.cancel()).to_equal(true)
expect(session.cancel()).to_equal(true)
val terminal = session.status()
print "cancel evidence accepted={accepted} depth={inbox.depth()} cancelled={terminal.cancelled} closed={terminal.closed} alive={terminal.alive} attempts={terminal.close_attempts} reason={terminal.terminal_reason}"
expect(terminal.cancelled).to_equal(true)
expect(terminal.closed).to_equal(true)
expect(terminal.alive).to_equal(false)
expect(terminal.close_attempts).to_equal(1)
expect(terminal.terminal_reason).to_equal("cancelled")
expect(inbox.depth()).to_equal(0)
expect(inbox.receive().reason).to_equal("closed")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c32c322d2914b0794b979f0d940b837663b84942f9f7fac5758ee1408c860027`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c32c322d2914b0794b979f0d940b837663b84942f9f7fac5758ee1408c860027`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c32c322d2914b0794b979f0d940b837663b84942f9f7fac5758ee1408c860027`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **84/100**; blockers: **0**.

SSpec documentization score: 84/100
source: 03_system/feature/language/parent_commit_piped_result_spec.spl
mirror: doc/06_spec/03_system/feature/language/parent_commit_piped_result_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=55 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
03_system/feature/language/parent_commit_piped_result_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 20 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
03_system/feature/language/parent_commit_piped_result_spec.spl:260:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should retain an owned copy before the producer mutates its frame' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
03_system/feature/language/parent_commit_piped_result_spec.spl:278:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should roll back a mixed valid and malformed process batch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
03_system/feature/language/parent_commit_piped_result_spec.spl:313:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should cancel a live child and revoke its accepted result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
doc/06_spec/03_system/feature/language/parent_commit_piped_result_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/feature/language/parent_commit_piped_result_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/language/parent_commit_piped_result_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
