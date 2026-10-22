# Host process-event data contracts

Status: **13 PASS / 0 FAIL — non-admitting retained historical-seed diagnostic**. The coordinator ran this frozen canonical file once: 273 ms, exit 0, peak RSS 217068 KiB, enforced limit 5859375 KiB, quiescent=1. Evidence is `build/phase-one-storage-gui-diagnostic/replay_process_event_spec/cycle-one.log`, sibling resource/exit receipts and `process-event-cycle-one-inputs.sdn`. All ten original cases and three added cases passed. The canonical source hash remained unchanged; no passing case was rerun.

The retained seed is SHA-256 `0cceac635e63781b7bf9bc9830735e948986de223434eca46d84eb35233f8b17`; its seven retained-generation bindings were independently verified in `/tmp/retained-phase1-seed-provenance-review-20261011.md`. The mutable marker `/tmp/beta-qual-4159b0b6/src/compiler_rust/target/bootstrap.current.env` and preflight `/tmp/beta-qual-4159b0b6/.simple/storage/build/bootstrap/bootstrap-preflight.env` are absent. Retained identity establishes which historical producer executed this diagnostic; it does not establish current Phase1 admission, fresh preflight, normal fullCLI/native or release qualification. No authority pointer was recreated, and resource containment is not compiler admission.

This host-only diagnostic is complete. No production source, shared guide or other replay lane changed; no VM, guest, QEMU or process-launch operation was exercised. No further runtime execution is planned.

## Actual behavior

The original cases inspect real enum conversions and constructor payloads. Added cases check every public kind ID/name in both directions against explicit values, the existing out-of-range fallback, every field produced by all four constructors, negative syscall results/arguments, zeroed unused payload slots and exact production summary text. The assertion helpers only inspect actual returned values; they do not implement the production conversion or constructors. No source-text assertions are used.

`ProcessEventKind.from_i32` currently maps unknown IDs to SyscallEntry. This records compatibility behavior, not strict input validation. The source comment's 60-byte record layout is not verified by these data-model tests; no binary serializer is invoked.

## Ownership, dependencies and qualification limits

Production owner: `src/lib/nogc_sync_mut/replay/process/event_types.spl` (SHA-256 `984b750a9e375f1436f4323057a0b622b0006b7e6bc557145755c7b5579f62b6`), a leaf with no imports. The executable spec imports that owner and the shared `std.spec` harness. The coordinator's execution manifest must bind the actual harness/producer closure as well as these source inputs. No concrete production defect was found during this scoped static intake; any runtime finding needs separate source authorization.

These are host-only in-memory data contracts. They require no process launch, ptrace, strace, process recorder/replayer, checkpoint, filesystem operation, QEMU, guest or VM execution. This file does not establish live process replay, native behavior, binary record layout, current Phase1 admission, fullCLI or release qualification. The actual retained historical-seed provenance and missing current-authority pointers are recorded above; this remains non-admitting evidence.

Requirement trace: `REQ-SSPEC-SYSTEM`. The 80% coverage annotation is an admission target, not measured coverage. Every scenario has a visible step and real assertions. This manual mirrors the source exactly; SPipe docgen remains pending.

The original canonical and `test/system/replay_process_event_spec.spl` were byte-identical, SHA-256 `36c0d129d819581a7f29eccdc3c43f17ba09432fd31cfa3fcd6ae7a72ebc9adb`. The duplicate was removed after preserving all ten original cases and assertions; no additional legacy requirement or tag existed. Bounded searches found no explicit legacy-path references in scripts, app source or system-test plans.

Canonical SHA-256: `346e5d3a7f5d8d6e5c5dee74c8aed3960241ba0080008e61179ddbc2fb743dfa`. Prepared inputs are recorded in `build/phase-one-storage-gui-diagnostic/replay-process-event-prepared.sdn`. The first and only baseline selected all 13 cases once. All passed; no retry or already-green process/semantic/VM lane is selected.

## Scenarios and visible steps

| Case | Scenario | Evidence |
|---|---|---|
| 1 | SyscallEntry to_i32 returns 0 | Diagnostic PASS |
| 2 | SyscallExit to_i32 returns 1 | Diagnostic PASS |
| 3 | Signal to_i32 returns 2 | Diagnostic PASS |
| 4 | ProcessExit to_i32 returns 9 | Diagnostic PASS |
| 5 | syscall_entry sets kind to SyscallEntry | Diagnostic PASS |
| 6 | syscall_entry stores syscall number in payload_a | Diagnostic PASS |
| 7 | syscall_exit stores retval in payload_a | Diagnostic PASS |
| 8 | signal_event sets kind to Signal | Diagnostic PASS |
| 9 | exit_event stores exit_code in payload_a | Diagnostic PASS |
| 10 | event_kind() roundtrips for SyscallExit | Diagnostic PASS |
| 11 | preserves all event identities and the existing invalid-ID fallback | Diagnostic PASS |
| 12 | preserves every syscall-entry field and renders its exact summary | Diagnostic PASS |
| 13 | preserves exit and signal payloads with clean unused fields | Diagnostic PASS |

<details>
<summary>Exact executable SSpec source</summary>

```simple
# codex-system-test
# @req REQ-SSPEC-SYSTEM
# @cover src/lib/nogc_sync_mut/replay/process/event_types.spl 80%
# Coverage percentage is an admission target, not measured coverage.
# @tag:system
# Host-only event data contracts; no process launch, ptrace, guest or VM execution.

use std.spec.{describe, it, expect, step}
use std.nogc_sync_mut.replay.process.event_types.{ProcessEventKind, ProcessReplayEvent}

fn expect_process_kind(kind: ProcessEventKind, code: i32, label: text):
    expect(kind.to_i32()).to_equal(code)
    expect(kind.to_text()).to_equal(label)
    val recovered = ProcessEventKind.from_i32(code)
    expect(recovered.to_i32()).to_equal(code)
    expect(recovered.to_text()).to_equal(label)

fn expect_process_record(ev: ProcessReplayEvent, seq: i64, tid: i64, kind: i32, timestamp: i64, a: i64, b: i64, c: i64):
    expect(ev.seq).to_equal(seq)
    expect(ev.tid).to_equal(tid)
    expect(ev.kind).to_equal(kind)
    expect(ev.timestamp_ns).to_equal(timestamp)
    expect(ev.payload_a).to_equal(a)
    expect(ev.payload_b).to_equal(b)
    expect(ev.payload_c).to_equal(c)
    expect(ev.payload_d).to_equal(0)

describe "ProcessEventKind to_i32":
    it "SyscallEntry to_i32 returns 0":
        step("SyscallEntry to_i32 returns 0")
        val k = ProcessEventKind.SyscallEntry
        expect(k.to_i32()).to_equal(0)

    it "SyscallExit to_i32 returns 1":
        step("SyscallExit to_i32 returns 1")
        val k = ProcessEventKind.SyscallExit
        expect(k.to_i32()).to_equal(1)

    it "Signal to_i32 returns 2":
        step("Signal to_i32 returns 2")
        val k = ProcessEventKind.Signal
        expect(k.to_i32()).to_equal(2)

    it "ProcessExit to_i32 returns 9":
        step("ProcessExit to_i32 returns 9")
        val k = ProcessEventKind.ProcessExit
        expect(k.to_i32()).to_equal(9)

describe "ProcessReplayEvent constructors":
    it "syscall_entry sets kind to SyscallEntry":
        step("syscall_entry sets kind to SyscallEntry")
        val ev = ProcessReplayEvent.syscall_entry(1, 100, 999, 60, 0, 0)
        expect(ev.kind).to_equal(ProcessEventKind.SyscallEntry.to_i32())

    it "syscall_entry stores syscall number in payload_a":
        step("syscall_entry stores syscall number in payload_a")
        val ev = ProcessReplayEvent.syscall_entry(1, 100, 999, 60, 0, 0)
        expect(ev.payload_a).to_equal(60)

    it "syscall_exit stores retval in payload_a":
        step("syscall_exit stores retval in payload_a")
        val ev = ProcessReplayEvent.syscall_exit(2, 100, 1000, 42)
        expect(ev.payload_a).to_equal(42)

    it "signal_event sets kind to Signal":
        step("signal_event sets kind to Signal")
        val ev = ProcessReplayEvent.signal_event(3, 200, 2000, 9)
        expect(ev.kind).to_equal(ProcessEventKind.Signal.to_i32())

    it "exit_event stores exit_code in payload_a":
        step("exit_event stores exit_code in payload_a")
        val ev = ProcessReplayEvent.exit_event(4, 300, 3000, 1)
        expect(ev.payload_a).to_equal(1)

    it "event_kind() roundtrips for SyscallExit":
        step("event_kind() roundtrips for SyscallExit")
        val ev = ProcessReplayEvent.syscall_exit(5, 1, 100, 0)
        val k = ev.event_kind()
        expect(k.to_i32()).to_equal(1)

describe "Complete host process-event data contracts":
    it "preserves all event identities and the existing invalid-ID fallback":
        step("Check all ten production kinds against explicit IDs and names")
        expect_process_kind(ProcessEventKind.SyscallEntry, 0, "syscall_entry")
        expect_process_kind(ProcessEventKind.SyscallExit, 1, "syscall_exit")
        expect_process_kind(ProcessEventKind.Signal, 2, "signal")
        expect_process_kind(ProcessEventKind.MmapResult, 3, "mmap_result")
        expect_process_kind(ProcessEventKind.TimeQuery, 4, "time_query")
        expect_process_kind(ProcessEventKind.RandomBytes, 5, "random_bytes")
        expect_process_kind(ProcessEventKind.Checkpoint, 6, "checkpoint")
        expect_process_kind(ProcessEventKind.ThreadSwitch, 7, "thread_switch")
        expect_process_kind(ProcessEventKind.ProcessCreate, 8, "process_create")
        expect_process_kind(ProcessEventKind.ProcessExit, 9, "process_exit")

        step("Inspect the existing fallback below and above the defined ID range")
        val negative = ProcessEventKind.from_i32(-1)
        val past_last = ProcessEventKind.from_i32(10)
        expect(negative.to_i32()).to_equal(0)
        expect(negative.to_text()).to_equal("syscall_entry")
        expect(past_last.to_i32()).to_equal(0)
        expect(past_last.to_text()).to_equal("syscall_entry")

    it "preserves every syscall-entry field and renders its exact summary":
        step("Create an entry with distinct sequence, thread, time and arguments")
        val ev = ProcessReplayEvent.syscall_entry(17, 301, 987654, 64, 4096, -7)
        expect_process_record(ev, 17, 301, 0, 987654, 64, 4096, -7)

        step("Inspect the resolved kind and the production diagnostic summary")
        expect(ev.event_kind().to_text()).to_equal("syscall_entry")
        expect(ev.summary()).to_equal("[17] tid=301 syscall_entry a=64 b=4096")

    it "preserves exit and signal payloads with clean unused fields":
        step("Create a syscall exit with a negative result")
        val returned = ProcessReplayEvent.syscall_exit(21, 101, 1001, -13)
        expect_process_record(returned, 21, 101, 1, 1001, -13, 0, 0)
        expect(returned.summary()).to_equal("[21] tid=101 syscall_exit a=-13 b=0")

        step("Create a signal event and inspect its complete payload")
        val signaled = ProcessReplayEvent.signal_event(22, 102, 1002, 15)
        expect_process_record(signaled, 22, 102, 2, 1002, 15, 0, 0)
        expect(signaled.event_kind().to_text()).to_equal("signal")

        step("Create a process exit and inspect its complete payload")
        val exited = ProcessReplayEvent.exit_event(23, 103, 1003, 127)
        expect_process_record(exited, 23, 103, 9, 1003, 127, 0, 0)
        expect(exited.event_kind().to_text()).to_equal("process_exit")
```

</details>
