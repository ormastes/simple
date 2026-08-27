# Parent-authoritative piped child-result evidence

> This executable system specification exercises the real process-transfer path

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
| Updated | 2026-08-26 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PAR-002
# @req REQ-PAR-003
# @req REQ-PAR-005
# @req REQ-PAR-006
# @req REQ-PAR-008
# @req REQ-PAR-009
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-PAR-002`
- `REQ-PAR-003`
- `REQ-PAR-005`
- `REQ-PAR-006`
- `REQ-PAR-008`
- `REQ-PAR-009`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2e156d74e70dfd705bd1ff90114904c97fda5598ed6abc9332f15ed740a15852`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2e156d74e70dfd705bd1ff90114904c97fda5598ed6abc9332f15ed740a15852`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2e156d74e70dfd705bd1ff90114904c97fda5598ed6abc9332f15ed740a15852`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/03_system/feature/language/parent_commit_piped_result_spec.spl
mirror: doc/06_spec/03_system/feature/language/parent_commit_piped_result_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/language/parent_commit_piped_result_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/language/parent_commit_piped_result_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/language/parent_commit_piped_result_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/language/parent_commit_piped_result_spec.spl:125:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should validate, commit, and close one fragmented child result' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/feature/language/parent_commit_piped_result_spec.spl:125:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should validate, commit, and close one fragmented child result' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/language/parent_commit_piped_result_spec.spl:260:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain an owned copy before the producer mutates its frame' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/language/parent_commit_piped_result_spec.spl:260:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should retain an owned copy before the producer mutates its frame' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/language/parent_commit_piped_result_spec.spl:278:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should roll back a mixed valid and malformed process batch' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/language/parent_commit_piped_result_spec.spl:278:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should roll back a mixed valid and malformed process batch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/language/parent_commit_piped_result_spec.spl:313:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should cancel a live child and revoke its accepted result' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/language/parent_commit_piped_result_spec.spl:313:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should cancel a live child and revoke its accepted result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
