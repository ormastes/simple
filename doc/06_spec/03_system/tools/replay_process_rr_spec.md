# Replay Process Recorder, Cursor and Checkpoint Model Specification

Status: **host-only model diagnostic passed**. The coordinator executed all 22 cases once: **22 passed, zero failed, zero skipped, zero dropped**, in **374 ms**, exit **0**. This retained historical-seed diagnostic is explicitly **non-admitting**; current Phase1/full CLI/native admission is not available from historical generation integrity. No production edits or runtime defect are claimed. Passing cases were not rerun.

Canonical source: `test/03_system/tools/replay_process_rr_spec.spl`.
Requirement: `REQ-SSPEC-SYSTEM`. Evidence class: **host-fixture / in-memory model**. All **22 existing cases** were retained and executed with stronger payload and state assertions. These are historical interpreter diagnostic counts, not native binary registration counts.

## Diagnostic evidence

Evidence root: `build/phase-one-storage-gui-diagnostic/`. Log, resource receipt and exit status: `replay_process_rr_spec/cycle-one.{log,rss.env,exit}`. Frozen manifest: `process-rr-cycle-one-inputs.sdn`, covering **44 inputs**. The resource receipt reports completion and peak process-tree RSS **222784 KiB**; the coordinator reports quiescence **1**.

Canonical source SHA-256: `038522ce8b50b9080b6466de1a8fcecb982cde353b8d2e1a0cff2c371aaa9b80`. The tested source and original `replay_process_rr_spec/baseline-plan.sdn` remain frozen. Separate `replay_process_rr_spec/baseline-status.sdn` records the actual result. One cycle was used; convergence stops execution without spending the remaining two cycles.

The retained historical seed is identified by SHA-256 `0cceac635e63781b7bf9bc9830735e948986de223434eca46d84eb35233f8b17`. The mutable current marker and preflight are absent; they were not recreated. Retained-generation identity does not replace current compiler admission. Provenance assessment: `/tmp/retained-phase1-seed-provenance-review-20261011.md`. No actual target-process execution, shell/strace invocation, trace-file I/O, VM or QEMU call occurs in these model scenarios.

## Host-only eligibility and source closure

Every scenario invokes pure host-model constructors, callbacks or collection queries. `ProcessRecorder.create` stores its command string; it does not execute it. `on_syscall_enter`, `on_syscall_exit` and `on_signal` construct and append `ProcessReplayEvent` values. `ProcessReplayer.create`, event queries and `step_forward` operate on caller-supplied arrays. Its automatic checkpoint path calls `CheckpointManager.take_checkpoint`, which creates and stores an empty `PageCheckpoint` without process access. Dirty pages and register entries are supplied data values, not captured process memory.

No scenario calls `record`, `start_recording`, recorder `stop`, trace `load`, `save_process_checkpoint` or `restore_process_checkpoint`. Consequently, this file does not launch commands, invoke strace, read/write `/proc`, access trace files, boot a guest or require QEMU/VM execution. No live integration case was removed or replaced to obtain host eligibility.

Existing `std.replay.process.*` imports are preserved. Source inspection follows their real `gc_sync_mut -> gc_async_mut -> nogc_async_mut -> nogc_sync_mut` forwarding modules; their prior spelling is not presumed broken. Physical exercised owners are `src/lib/nogc_sync_mut/replay/process/{event_types,recorder,replayer,checkpoint}.spl`. `replayer.spl` additionally imports `trace_io.spl`, and several owners import `io.process_ops`; those I/O functions are not called by this spec. The four 80% coverage annotations are targets, not measured results or coverage of their live paths.

## Manual flow

1. Construct a recorder and check idle mode, empty events, initial PID, sequence and pending-syscall state.
2. Feed entry, exit and signal callbacks. Guard event counts before indexing, then compare actual sequence, thread identity, kinds and payloads. Confirm pending-syscall state is set and cleared as expected.
3. Check monotonic ordering across a mixed recorded event sequence.
4. Construct a replayer model, supply recorded values, query without advancing, and consume two distinct events in order. Confirm exhaustion returns `None` and does not advance again.
5. Query a valid event index and the explicitly guarded negative/end indices; require unchanged cursor state.
6. Create checkpoint metadata, check IDs and event sequence, and confirm empty process-state collections. Query empty managers and closest/exact event boundaries, preserving the stored checkpoint count.
7. Construct dirty-page and register values, compare actual page bytes, retrieve the supplied register, and preserve missing-register and PID metadata checks.

`step_forward` returns the production model's `Match` verdict without independently executing another process. Testing that verdict and its event summary proves cursor/model behavior only. Checkpoint selection proves metadata navigation, not restored registers/memory or replay-forward execution. Live strace/ptrace capture, permission-dependent process memory I/O, durable trace persistence and independent process replay verification remain **OPEN / unqualified**.

Legacy `test/system/replay_process_rr_spec.spl` was removed only after full-file `cmp` proved byte identity with the pre-edit canonical file. Both originals had SHA-256 `99393d1726a733fb8b6386d51956740c34c64ec3a8ba2006639718e2d33034c7`. All original case names and assertions remain; added checks strengthen their existing contracts.

## Complete executable source

<details>
<summary>Executable SSpec</summary>

```simple
# codex-system-test
# @req REQ-SSPEC-SYSTEM
# @tag:system
# @cover src/lib/nogc_sync_mut/replay/process/event_types.spl 80%
# @cover src/lib/nogc_sync_mut/replay/process/recorder.spl 80%
# @cover src/lib/nogc_sync_mut/replay/process/replayer.spl 80%
# @cover src/lib/nogc_sync_mut/replay/process/checkpoint.spl 80%
# Coverage percentages are targets, not measured coverage.
# Host-only in-memory model: callbacks, recorded-event cursor and checkpoint data.
# No VM, guest, QEMU, subprocess, strace, /proc access or trace-file I/O is invoked.
# step_forward reports a model Match without comparison to an independent process.
# Live process record/replay and memory/register restoration remain unqualified.

use std.spec
use std.replay.process.event_types.{ProcessEventKind, ProcessReplayEvent}
use std.replay.process.recorder.{ProcessRecorder, RecordingMode}
use std.replay.process.replayer.{ProcessReplayer, ReplayVerdict}
use std.replay.process.checkpoint.{DirtyPage, RegisterEntry, PageCheckpoint, CheckpointManager}

# ============================================================================
# ProcessRecorder — in-memory stream API (no shell)
# ============================================================================

describe "ProcessRecorder creation":
    it "creates with Idle mode":
        step("Construct the recorder model without launching its command")
        val rec = ProcessRecorder.create("echo hello", "/tmp/test_trace")
        expect(rec.command).to_equal("echo hello")
        expect(rec.events.len()).to_equal(0)
        expect(rec.next_seq).to_equal(0)
        expect(rec.mode == RecordingMode.Idle).to_equal(true)
        expect(rec.pid).to_equal(0)
        expect(rec.pending_syscall_id).to_equal(-1)

    it "on_syscall_enter records entry event":
        step("Supply a syscall callback and inspect the stored event payload")
        var rec = ProcessRecorder.create("cmd", "/tmp/t")
        rec.pid = 100
        rec.on_syscall_enter(1, [42, 0])
        expect(rec.events.len()).to_equal(1)
        if rec.events.len() != 1:
            return
        expect(rec.events[0].payload_a).to_equal(1)
        expect(rec.events[0].seq).to_equal(0)
        expect(rec.events[0].tid).to_equal(100)
        expect(rec.events[0].kind).to_equal(ProcessEventKind.SyscallEntry.to_i32())
        expect(rec.events[0].timestamp_ns).to_equal(0)
        expect(rec.events[0].payload_b).to_equal(42)
        expect(rec.events[0].payload_c).to_equal(0)
        expect(rec.events[0].payload_d).to_equal(0)
        expect(rec.pending_syscall_id).to_equal(1)
        expect(rec.next_seq).to_equal(1)

    it "on_syscall_exit records exit event":
        step("Supply paired entry and exit callbacks and inspect the recorded exit")
        var rec = ProcessRecorder.create("cmd", "/tmp/t")
        rec.pid = 100
        rec.on_syscall_enter(1, [])
        rec.on_syscall_exit(0)
        expect(rec.events.len()).to_equal(2)
        if rec.events.len() != 2:
            return
        expect(rec.events[1].seq).to_equal(1)
        expect(rec.events[1].tid).to_equal(100)
        expect(rec.events[1].kind).to_equal(ProcessEventKind.SyscallExit.to_i32())
        expect(rec.events[1].payload_a).to_equal(0)
        expect(rec.pending_syscall_id).to_equal(-1)
        expect(rec.next_seq).to_equal(2)

    it "on_signal records signal event":
        step("Supply a signal callback and read its thread and signal identity")
        var rec = ProcessRecorder.create("cmd", "/tmp/t")
        rec.pid = 200
        rec.on_signal(9)
        expect(rec.events.len()).to_equal(1)
        if rec.events.len() != 1:
            return
        val kind = ProcessEventKind.from_i32(rec.events[0].kind)
        expect(kind.to_text()).to_equal("signal")
        expect(rec.events[0].seq).to_equal(0)
        expect(rec.events[0].tid).to_equal(200)
        expect(rec.events[0].payload_a).to_equal(9)

    it "sequence numbers are monotonic across mixed events":
        step("Supply mixed callbacks and inspect their stored sequence order")
        var rec = ProcessRecorder.create("cmd", "/tmp/t")
        rec.pid = 50
        rec.on_syscall_enter(1, [])
        rec.on_syscall_exit(0)
        rec.on_signal(15)
        expect(rec.events.len()).to_equal(3)
        if rec.events.len() != 3:
            return
        expect(rec.events[0].seq).to_equal(0)
        expect(rec.events[1].seq).to_equal(1)
        expect(rec.events[2].seq).to_equal(2)

# ============================================================================
# ProcessReplayer — in-memory stepping
# ============================================================================

describe "ProcessReplayer stepping":
    it "create starts at position 0":
        val rpl = ProcessReplayer.create("/tmp/trace")
        expect(rpl.position()).to_equal(0)
        expect(rpl.event_count()).to_equal(0)
        expect(rpl.has_more()).to_equal(false)

    it "has_more is true when events exist":
        var rpl = ProcessReplayer.create("/tmp/trace")
        val ev = ProcessReplayEvent.syscall_exit(0, 1, 0, 42)
        rpl.events = [ev]
        expect(rpl.has_more()).to_equal(true)
        expect(rpl.event_count()).to_equal(1)

    it "step_forward returns None at end":
        var rpl = ProcessReplayer.create("/tmp/trace")
        val result = rpl.step_forward()
        expect(result.is_none()).to_equal(true)

    it "step_forward advances cursor and returns result":
        step("Load two recorded model events and consume them in order")
        var rpl = ProcessReplayer.create("/tmp/trace")
        val ev0 = ProcessReplayEvent.syscall_exit(0, 1, 0, 10)
        val ev1 = ProcessReplayEvent.syscall_exit(1, 1, 0, 20)
        rpl.events = [ev0, ev1]
        val first = rpl.step_forward()
        match first:
            case Some(r):
                expect(r.event_seq).to_equal(0)
                expect(r.verdict == ReplayVerdict.Match).to_equal(true)
                expect(r.message).to_contain("syscall_exit a=10")
            case None:
                expect("should have result").to_equal("")
        expect(rpl.position()).to_equal(1)
        match rpl.step_forward():
            case Some(r):
                expect(r.event_seq).to_equal(1)
                expect(r.message).to_contain("syscall_exit a=20")
            case None:
                fail("second recorded model event was not returned")
        expect(rpl.position()).to_equal(2)
        expect(rpl.has_more()).to_equal(false)
        val exhausted_step = rpl.step_forward()
        val exhausted_current = rpl.current_event()
        expect(exhausted_step.is_none()).to_equal(true)
        expect(exhausted_current.is_none()).to_equal(true)
        expect(rpl.position()).to_equal(2)

    it "current_event returns event without advancing":
        var rpl = ProcessReplayer.create("/tmp/trace")
        val ev = ProcessReplayEvent.signal_event(0, 10, 0, 9)
        rpl.events = [ev]
        val cur = rpl.current_event()
        match cur:
            case Some(e):
                expect(e.payload_a).to_equal(9)
            case None:
                expect("should have event").to_equal("")
        expect(rpl.position()).to_equal(0)

    it "event_at returns event by index":
        step("Query a stored event and reject documented out-of-range lookups without moving the cursor")
        var rpl = ProcessReplayer.create("/tmp/trace")
        val ev0 = ProcessReplayEvent.syscall_exit(0, 1, 0, 10)
        val ev1 = ProcessReplayEvent.syscall_exit(1, 1, 0, 20)
        rpl.events = [ev0, ev1]
        match rpl.event_at(1):
            case Some(e):
                expect(e.payload_a).to_equal(20)
            case None:
                expect("should have event").to_equal("")
        val before_start = rpl.event_at(-1)
        val past_end = rpl.event_at(2)
        expect(before_start.is_none()).to_equal(true)
        expect(past_end.is_none()).to_equal(true)
        expect(rpl.position()).to_equal(0)

# ============================================================================
# CheckpointManager
# ============================================================================

describe "CheckpointManager":
    it "starts with zero checkpoints":
        val mgr = CheckpointManager.create()
        expect(mgr.count()).to_equal(0)

    it "create initializes next_id to 0":
        val mgr = CheckpointManager.create()
        expect(mgr.next_id).to_equal(0)
        expect(mgr.checkpoints.len()).to_equal(0)

    it "take_checkpoint increments next_id":
        step("Create checkpoint metadata without capturing a live process")
        var mgr = CheckpointManager.create()
        val cp = mgr.take_checkpoint(100)
        expect(cp.checkpoint_id).to_equal(0)
        expect(cp.event_seq).to_equal(100)
        expect(cp.pid).to_equal(0)
        expect(cp.register_state.len()).to_equal(0)
        expect(cp.dirty_pages.len()).to_equal(0)
        expect(mgr.next_id).to_equal(1)
        expect(mgr.count()).to_equal(1)

    it "find_checkpoint returns None on empty manager":
        val mgr = CheckpointManager.create()
        val result = mgr.find_checkpoint(0)
        expect(result.is_none()).to_equal(true)

    it "nearest_before returns None on empty manager":
        val mgr = CheckpointManager.create()
        val result = mgr.nearest_before(100)
        expect(result.is_none()).to_equal(true)

    it "nearest_before returns closest checkpoint":
        step("Select the closest stored checkpoint and include an exact event boundary")
        var mgr = CheckpointManager.create()
        mgr.take_checkpoint(10)
        mgr.take_checkpoint(50)
        mgr.take_checkpoint(100)
        val result = mgr.nearest_before(60)
        match result:
            case Some(cp):
                expect(cp.event_seq).to_equal(50)
            case None:
                expect("should find checkpoint").to_equal("")
        match mgr.nearest_before(50):
            case Some(cp):
                expect(cp.checkpoint_id).to_equal(1)
                expect(cp.event_seq).to_equal(50)
            case None:
                fail("checkpoint at exact event boundary was not found")
        val before_first = mgr.nearest_before(9)
        expect(before_first.is_none()).to_equal(true)
        expect(mgr.count()).to_equal(3)

    it "latest returns None on empty manager":
        val mgr = CheckpointManager.create()
        val result = mgr.latest()
        expect(result.is_none()).to_equal(true)

# ============================================================================
# DirtyPage / PageCheckpoint construction (process-level)
# ============================================================================

describe "DirtyPage and PageCheckpoint":
    it "DirtyPage.create stores addr and data":
        step("Create a page data value and compare its actual bytes")
        val page = DirtyPage.create(4096, [0, 1, 2, 3])
        expect(page.addr).to_equal(4096)
        expect(page.data.len()).to_equal(4)
        expect(page.data).to_equal([0, 1, 2, 3])

    it "PageCheckpoint add_register stores value":
        var cp = PageCheckpoint.create(0, 100)
        cp.add_register("rip", 12345)
        match cp.get_register("rip"):
            case Some(v):
                expect(v).to_equal(12345)
            case None:
                expect("should find register").to_equal("")

    it "PageCheckpoint get_register returns None for missing":
        val cp = PageCheckpoint.create(0, 0)
        val result = cp.get_register("nonexistent")
        expect(result.is_none()).to_equal(true)

    it "PageCheckpoint.create_for_pid stores pid":
        val cp = PageCheckpoint.create_for_pid(1, 500, 9999)
        expect(cp.pid).to_equal(9999)
        expect(cp.event_seq).to_equal(500)
```

</details>
