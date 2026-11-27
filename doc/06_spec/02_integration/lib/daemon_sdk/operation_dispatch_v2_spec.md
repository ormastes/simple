# Retained operation outcomes and response delivery

**AUTHORED_NOT_RUN.** Modern SSpec manual authored from the executable source;
not a generated or executed report. `spipe-docgen` validation (complete, zero
stubs) and compiled execution are pending the admitted full CLI/test runner.

Source: `test/02_integration/lib/daemon_sdk/operation_dispatch_v2_spec.spl`.
Requirements: DAE-01, DAE-03. Acceptance: AT-DAE-03 and **partial AT-DAE-01**.
Evidence class: real local journal/file integration with injected callback faults.

## Setup and isolation

Each scenario opens a unique private directory through `secure_temp_dir` and the
production journal opener. Synthetic request identity and result bytes are test
data, not authenticated grants. A completed fixture commits admission, execution
intent and the digest of actual result-file bytes in order.

Cleanup closes only that scenario's original journal before removing its private
root. A close error or an unconfirmed close records failure and returns without
deleting the directory. No runtime-global cleanup occurs. Unexpected setup or
body unwrap failure can retain fixture data/locks; this suite does not qualify
cleanup after arbitrary fixture crashes or replace protected Host owner tests.

## Scenarios

| Scenario | Steps and observable result |
| --- | --- |
| Immutable admission | Open the isolated real operation journal; admit one request; repeat it; change its payload. Assert NEWLY_ADMITTED, ALREADY_ADMITTED, sequence 1 and exact OPERATION_PAYLOAD_MISMATCH. |
| Execution intent | Admit the exact operation and publish its execution intent. Reject terminal state before intent, a second begin, and the stale pre-intent owner. |
| Failed publication | Persist terminal bytes and a request file; inject failed publication. Observe retained state after response or acknowledgement failure: exact RESPONSE_PUBLICATION_FAILED, completed state/digest, original request bytes, and no response file. The forbidden acknowledgement callback records failure if reached. |
| Retained delivery after reopen | Close and reopen the same journal. Assert RETAINED_OUTCOME and sequence 3; publish exact retained bytes and delete only the request. Assert response equality, request absence and refusal of another begin. |
| Failed acknowledgement | Publish the real response file and inject failed acknowledgement. Assert exact REQUEST_ACKNOWLEDGEMENT_FAILED, unchanged response/request bytes and RETAINED_OUTCOME. |
| Disclosure guard | Submit changed result bytes and changed session generation. Reject with exact OUTCOME_BYTES_MISMATCH / OPERATION_PAYLOAD_MISMATCH before either forbidden callback. |
| Terminal immutability | Reject nonterminal publication and nonterminal outcome recording. Replay the same terminal outcome without a new commit (sequence 3); reject changed state and digest. |
| Unknown recovery | Reopen an executing journal and invoke the production recovery transition. Reject a new begin with exact OUTCOME_UNKNOWN and preserve duplicate state outcome-unknown. |

All eight registered cases retain their original production assertions; six
additional assertions check actual request/response file effects. Close only the
exact fixture journal at the end of each successful path.

## Qualification boundary

This suite does not launch an external command, kill/restart a daemon, interrupt
a native effect, exercise power-loss flush/compaction, or authenticate a caller.
Injected callbacks are delivery fault tests, not observed native process crashes.
It cannot close full AT-DAE-01 or AT-DAE-04. Source case/assertion counts are not
executed counts. Preserve explicit AOT compilation and runtime results separately.

<details>
<summary>Executable SSpec source (authored, unexecuted)</summary>

```simple
# codex-system-test
# @req DAE-01 DAE-03
# @acceptance AT-DAE-01 AT-DAE-03
# AUTHORED_NOT_RUN: real local journal plus injected delivery callbacks.
# Partial AT-DAE-01 only: no native effect, process crash, or power-loss proof.
use std.spec.{describe, it, expect, fail, step}
use std.common.contracts.distributed_control_v2.OperationEnvelopeV2
use std.common.task_runner.distributed_operation_journal_v2.*
use std.nogc_sync_mut.daemon_sdk.operation_dispatch_v2.*
use std.nogc_sync_mut.io.file_ops.{secure_temp_dir, file_atomic_write, file_read}
use std.nogc_sync_mut.io_runtime.{dir_remove, file_delete, file_exists}
use std.common.crypto.sha256.sha256_text

fn request_fixture() -> OperationEnvelopeV2:
    OperationEnvelopeV2(version: 2, id: "operation_1", payload_digest: "a".repeat(64),
        principal: "user_1", project: "project_1", host_id: "host_1",
        operation: "agent_launch", environment_digest: "b".repeat(64),
        policy_revision: 1, revocation_epoch: 0, session_generation: 1,
        memory_bytes: 1024, duration_ms: 1000)

fn new_owner() -> DistributedOperationJournalV2:
    step("Open the isolated real operation journal")
    val root = secure_temp_dir("build", "daemon-operation-v2").unwrap()
    distributed_operation_journal_open_v2(root, "c".repeat(64), "d".repeat(64), 32).unwrap()

fn terminal_owner() -> DistributedOperationJournalV2:
    val original = new_owner()
    step("Admit the exact operation and publish its execution intent")
    val admitted = daemon_operation_admit_v2(original, request_fixture()).unwrap()
    val executing = daemon_operation_begin_v2(admitted.journal, request_fixture()).unwrap()
    val bytes = "status: completed\nresult: retained\n"
    expect(file_atomic_write(original.root + "/outcome.sdn", bytes)).to_equal(true)
    daemon_operation_record_outcome_v2(executing, request_fixture(), "completed", sha256_text(bytes)).unwrap()

fn cleanup(owner: DistributedOperationJournalV2):
    step("Close only the exact fixture journal")
    match distributed_operation_journal_close_v2(owner):
        case Err(reason):
            fail("fixture journal close failed: " + reason)
            return
        case Ok(closed):
            if not closed:
                fail("fixture journal close did not confirm release")
                return
    expect(dir_remove(owner.root, true)).to_equal(true)

fn forbidden_publish(id: text, bytes: text) -> bool:
    fail("publication was reached without a matching retained terminal outcome")
    false

fn forbidden_acknowledge(id: text) -> bool:
    fail("acknowledgement was reached before successful publication")
    false

fn reject_publish(id: text, bytes: text) -> bool:
    false

fn reject_acknowledge(id: text) -> bool:
    false

describe "shared daemon operations retain outcomes across response failure":
    it "should admit once and reject changed payload for the same identity":
        step("Admit one immutable request and compare duplicate and changed payloads")
        val original = new_owner()
        val first = daemon_operation_admit_v2(original, request_fixture()).unwrap()
        expect(first.disposition).to_equal("NEWLY_ADMITTED")
        val duplicate = daemon_operation_admit_v2(first.journal, request_fixture()).unwrap()
        expect(duplicate.disposition).to_equal("ALREADY_ADMITTED")
        expect(duplicate.journal.sequence).to_equal(1)
        var changed = request_fixture()
        changed.payload_digest = "e".repeat(64)
        match daemon_operation_admit_v2(first.journal, changed):
            case Ok(_): fail("changed payload admitted")
            case Err(reason): expect(reason).to_equal("OPERATION_PAYLOAD_MISMATCH")
        cleanup(first.journal)

    it "should require execution intent and refuse a second begin":
        step("Admit the exact operation and publish its execution intent")
        val original = new_owner()
        val admitted = daemon_operation_admit_v2(original, request_fixture()).unwrap()
        expect(daemon_operation_record_outcome_v2(admitted.journal, request_fixture(), "completed", "f".repeat(64)).is_err()).to_equal(true)
        val executing = daemon_operation_begin_v2(admitted.journal, request_fixture()).unwrap()
        match daemon_operation_begin_v2(executing, request_fixture()):
            case Ok(_): fail("execution was admitted twice")
            case Err(reason): expect(reason).to_equal("ALREADY_EXECUTING")
        expect(daemon_operation_begin_v2(admitted.journal, request_fixture()).is_err()).to_equal(true)
        cleanup(executing)

    it "should retain the request when response publication fails":
        step("Observe retained state after response or acknowledgement failure")
        val owner = terminal_owner()
        val outcome = file_read(owner.root + "/outcome.sdn")
        expect(file_atomic_write(owner.root + "/request", "operation_1")).to_equal(true)
        match daemon_operation_publish_v2(owner, request_fixture(), outcome, reject_publish, forbidden_acknowledge):
            case Ok(_): fail("failed publication reported success")
            case Err(reason): expect(reason).to_equal("RESPONSE_PUBLICATION_FAILED")
        val retained = distributed_operation_journal_lookup_v2(owner, "operation_1").unwrap()
        expect(retained.state).to_equal("completed")
        expect(retained.outcome_digest).to_equal(sha256_text(outcome))
        expect(file_read(owner.root + "/request")).to_equal("operation_1")
        expect(file_exists(owner.root + "/response.sdn")).to_equal(false)
        cleanup(owner)

    it "should reopen and publish the retained outcome without another execution":
        step("Reopen the same journal and reject another execution")
        val owner = terminal_owner()
        val root = owner.root
        val outcome = file_read(root + "/outcome.sdn")
        expect(daemon_operation_publish_v2(owner, request_fixture(), outcome, reject_publish, forbidden_acknowledge).is_err()).to_equal(true)
        expect(distributed_operation_journal_close_v2(owner).unwrap()).to_equal(true)
        val reopened = distributed_operation_journal_open_v2(root, "c".repeat(64), "e".repeat(64), 32).unwrap()
        val duplicate = daemon_operation_admit_v2(reopened, request_fixture()).unwrap()
        expect(duplicate.disposition).to_equal("RETAINED_OUTCOME")
        expect(duplicate.journal.sequence).to_equal(3)
        expect(file_atomic_write(root + "/request", "operation_1")).to_equal(true)
        val published = daemon_operation_publish_v2(reopened, request_fixture(), outcome,
            \id, bytes: file_atomic_write(root + "/response.sdn", bytes),
            \id: file_delete(root + "/request")).unwrap()
        expect(published).to_equal(true)
        expect(file_read(root + "/response.sdn")).to_equal(outcome)
        expect(file_exists(root + "/request")).to_equal(false)
        expect(daemon_operation_begin_v2(reopened, request_fixture()).is_err()).to_equal(true)
        cleanup(reopened)

    it "should retain the request and outcome after acknowledgement failure":
        step("Observe retained state after response or acknowledgement failure")
        val owner = terminal_owner()
        val root = owner.root
        val outcome = file_read(root + "/outcome.sdn")
        expect(file_atomic_write(root + "/request", "operation_1")).to_equal(true)
        match daemon_operation_publish_v2(owner, request_fixture(), outcome,
                \id, bytes: file_atomic_write(root + "/response.sdn", bytes), reject_acknowledge):
            case Ok(_): fail("failed acknowledgement reported success")
            case Err(reason): expect(reason).to_equal("REQUEST_ACKNOWLEDGEMENT_FAILED")
        expect(file_read(root + "/response.sdn")).to_equal(outcome)
        expect(file_read(root + "/request")).to_equal("operation_1")
        val duplicate = daemon_operation_admit_v2(owner, request_fixture()).unwrap()
        expect(duplicate.disposition).to_equal("RETAINED_OUTCOME")
        cleanup(owner)

    it "should reject mismatched bytes or requests before disclosure":
        step("Reject mismatched bytes and identity before either callback")
        val owner = terminal_owner()
        match daemon_operation_publish_v2(owner, request_fixture(), "changed", forbidden_publish, forbidden_acknowledge):
            case Ok(_): fail("changed outcome published")
            case Err(reason): expect(reason).to_equal("OUTCOME_BYTES_MISMATCH")
        var changed = request_fixture()
        changed.session_generation = 2
        val bytes = file_read(owner.root + "/outcome.sdn")
        match daemon_operation_publish_v2(owner, changed, bytes, forbidden_publish, forbidden_acknowledge):
            case Ok(_): fail("changed request published")
            case Err(reason): expect(reason).to_equal("OPERATION_PAYLOAD_MISMATCH")
        cleanup(owner)

    it "should reject nonterminal publication and changed terminal outcomes":
        step("Reject early publication and preserve the original terminal result")
        val original = new_owner()
        val admitted = daemon_operation_admit_v2(original, request_fixture()).unwrap()
        match daemon_operation_publish_v2(admitted.journal, request_fixture(), "", forbidden_publish, forbidden_acknowledge):
            case Ok(_): fail("nonterminal response published")
            case Err(reason): expect(reason).to_equal("OUTCOME_NOT_TERMINAL")
        expect(daemon_operation_record_outcome_v2(admitted.journal, request_fixture(), "executing", "").is_err()).to_equal(true)
        cleanup(admitted.journal)
        val owner = terminal_owner()
        val bytes = file_read(owner.root + "/outcome.sdn")
        val replay = daemon_operation_record_outcome_v2(owner, request_fixture(), "completed", sha256_text(bytes)).unwrap()
        expect(replay.sequence).to_equal(3)
        expect(daemon_operation_record_outcome_v2(owner, request_fixture(), "failed", sha256_text(bytes)).is_err()).to_equal(true)
        expect(daemon_operation_record_outcome_v2(owner, request_fixture(), "completed", "f".repeat(64)).is_err()).to_equal(true)
        cleanup(owner)

    it "should preserve outcome-unknown after recovery and refuse a new begin":
        step("Reopen the same journal and reject another execution")
        val original = new_owner()
        val admitted = daemon_operation_admit_v2(original, request_fixture()).unwrap()
        val executing = daemon_operation_begin_v2(admitted.journal, request_fixture()).unwrap()
        val root = executing.root
        expect(distributed_operation_journal_close_v2(executing).unwrap()).to_equal(true)
        val reopened = distributed_operation_journal_open_v2(root, "c".repeat(64), "e".repeat(64), 32).unwrap()
        val unknown = distributed_operation_journal_recover_execution_v2(reopened, "operation_1").unwrap()
        match daemon_operation_begin_v2(unknown, request_fixture()):
            case Ok(_): fail("unknown effect restarted")
            case Err(reason): expect(reason).to_equal("OUTCOME_UNKNOWN")
        val duplicate = daemon_operation_admit_v2(unknown, request_fixture()).unwrap()
        expect(duplicate.state).to_equal("outcome-unknown")
        cleanup(unknown)
```

</details>
