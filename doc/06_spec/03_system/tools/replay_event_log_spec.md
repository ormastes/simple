# Replay Event Log Specification

Status: **three reproduced host persistence failures repaired and verified**. Cycle one executed 30 cases: **27 passed, three failed**, in **1001 ms**, exit **1**. After the SOSIX repair, cycle two executed only the three failed cases: **three passed, zero failed**, in **223 ms**, exit **0**. Both runs reported zero skipped/dropped cases. The 27 passing cases were not rerun; no complete final-source 30-case rerun or third cycle is claimed. Evidence is explicitly **non-admitting historical-seed evidence**; current Phase1/full CLI, native, Windows, VM and full replay remain unqualified.

Canonical source: `test/03_system/tools/replay_event_log_spec.spl`.
Requirement: `REQ-SSPEC-SYSTEM`. Authored inventory: **30 cases**: all **26 original cases** retained and **four real persistence regressions**. The original cases exercise data contracts; added cases exercise production persistence on real host files. This source-synchronized manual records bounded diagnostic evidence, not docgen or native qualification.

## Diagnostic evidence

Evidence root: `build/phase-one-storage-gui-diagnostic/`. Baseline: `replay_event_log_spec/cycle-one.{log,rss.env,exit}`; frozen input manifest: `event-log-cycle-one-inputs.sdn`. All **67** baseline input hashes matched before and after execution. Peak process-tree RSS was **230168 KiB**; the coordinator reports quiescence **1**. The checked cleanup completed normally.

Final selected diagnostic: `replay-event-log-persistence-cycle-two_spec/cycle-two.{log,rss.env,exit}`; manifest: `event-log-cycle-two-inputs.sdn`. All **71** input hashes matched before and after execution. Peak process-tree RSS was **254868 KiB**, quiescence **1**, and the resource receipt reports completion with exit **0**. Separate final status: `replay_event_log_spec/final-status.sdn`. Frozen plans, source bindings and input manifests remain unchanged; this manual is not among the cycle-two frozen inputs.

Historical producer SHA-256: `0cceac635e63781b7bf9bc9830735e948986de223434eca46d84eb35233f8b17`. Current mutable marker/preflight are absent and were not recreated. The result is explicitly **non-admitting retained historical-seed evidence**, not current Phase1/full CLI authority.

Cycle two selected canonical cases **28, 29 and 30** through `replay-event-log-persistence-cycle-two_spec.spl` and `replay-event-log-persistence-cycle-two-mapping.sdn`. The rewrite fixture alone gained a nonempty read-back prerequisite comparing all twelve fields of both records through the repaired reader. This directly checked the materially changed byte conversion without rerunning the previously green round-trip case. Convergence ended execution after cycle two.

Final source SHA-256 values: event-log owner `b55165465bac8ed889e358122da337ca757187eaeee05c29b384fc012b5af5a6`; SOSIX facade `31ce0a227262901e6de7e3bf4d6f26ec2ad5b3e34f39530f71cd6c4d9ae63625`; canonical spec `16c00bebe8d825970cb5a90884e92d9ab267e8141d882f7e977ca30a0623ddf1`; selected derivative `4fe2e0d636bf54c9b42bf9b4dc7286aeae123c6a821b3e727215651e00dd7b7e`.

## Owners and host-only boundary

Production owners are `src/lib/nogc_sync_mut/replay/{event_log,types,event_kinds,codec}.spl`. The old kernel event-kind import was a compatibility facade over the same library record owner; this spec now names the library owner directly and avoids an unnecessary OS dependency. Coverage percentages are targets, not measured coverage.

The approved filesystem seam is `std.nogc_async_mut.sosix.host_facade`. Its new braced exports alias canonical `std.nogc_sync_mut.io_runtime.file_read_bytes_result`, `file_write_bytes`, and `read_file_text_result` to the corresponding `sosix_*` names. Strict byte/text read results retain errors, unlike lossy empty-on-error convenience reads. Existing SOSIX directory and atomic text writes supply fixture setup. No mock filesystem, separate filesystem registry, direct FAT32 dependency or SimpleOS boot dependency is introduced.

The baseline implementation used shell file operations. The repaired implementation removes those calls and unused hex helpers; it unconditionally writes actual bytes, including an empty array, and propagates strict text/binary read errors. The scenarios call the production methods; they do not install a replacement or simulate storage. No guest, QEMU, VM, application child or traced-process launch is involved. Portable/native/Windows qualification and durable storage guarantees remain separate.

## Manual persistence flow

1. Create a unique owned directory through `secure_temp_dir(".", "replay-event-log-owned")`. Creation failure fails the scenario; no existing path is reused.
2. Write two distinct production records, require 160 stored bytes, read through `read_event_log`, and compare architecture, event count, record order and all twelve fields of each record.
3. Persist two records, prove the nonempty byte-count prerequisite and decode both records through the repaired reader, checking all twelve fields. Then write an empty log to the same directory. Require an actually empty `events.bin` and zero decoded entries/count with architecture retained. This distinguishes truncation from merely updating a manifest or touching the old file.
4. Write a valid manifest into a fresh directory without an event file. Require `read_event_log` to return an error identifying `events.bin`, not a valid empty log.
5. Create a real directory at the `events.bin` destination and attempt to write an empty log. Require the production writer to report the failed event-file write. This does not depend on filesystem permission assumptions.
6. Remove only the directory returned by secure creation after each fixture callback, including ordinary error outcomes. Assert cleanup success. Runtime termination before callback return may leave that uniquely owned directory for coordinator cleanup; no broad shared-path cleanup is used.

Length guards prevent invalid indexing from obscuring a failed record-count assertion. Setup operations return explicit errors; unexpected production success on a negative case becomes a failed fixture result. SDN manifests remain SDN, and event bytes remain the existing 80-byte binary record format.

## Reproduced defects and repair

The original writer used unchecked `touch` for an empty log, leaving existing event bytes intact and ignoring failure. The original reader's `xxd | tr` pipeline could report success with empty output when the event file was missing. Cycle one reproduced all three failures; the unchanged complete round-trip case passed.

The repair routes directory/manifest/binary operations through the SOSIX seam, writes bytes unconditionally including empty arrays, preserves actual read errors, and removes the hex/shell workaround. Codec `[i32]` values are converted to/from provider `[u8]` values at this boundary. Cycle two verified repaired behavior for the selected historical producer. Durable close-error handling, two-file transactional publication, Windows binary mode, partial-record rejection, signed-negative codec values and full manifest metadata restoration remain outside this repair.

Legacy `test/system/replay_event_log_spec.spl` was removed only after full-file `cmp` proved equality with the pre-edit canonical source. Both originals had SHA-256 `39cd9ff3bba77cee75584122b4b053ce84bffd58cb981ab08497508cf4059739`. All 26 original case bodies are retained.

## Complete executable source

<details>
<summary>Executable SSpec, including real fixture helpers</summary>

```simple
# codex-system-test
# @req REQ-SSPEC-SYSTEM
# @tag:system
# @cover src/lib/nogc_sync_mut/replay/event_log.spl 80%
# @cover src/lib/nogc_sync_mut/replay/types.spl 80%
# @cover src/lib/nogc_sync_mut/replay/event_kinds.spl 80%
# @cover src/lib/nogc_sync_mut/replay/codec.spl 80%
# Coverage percentages are targets, not measured coverage.
# Host-only real filesystem fixtures; no VM, guest or traced-process launch.
# Baseline event_log still invokes its existing shell file operations.
# No native, full replay, process restoration or current compiler admission claim.

use std.spec
use std.nogc_sync_mut.replay.event_log.{TraceHeader, EventLog, write_event_log, read_event_log}
use std.nogc_sync_mut.replay.types.{Arch, Endian, TargetDesc}
use std.nogc_sync_mut.replay.event_kinds.{EventKind, ReplayEntry}
use std.nogc_async_mut.sosix.host_facade.{sosix_file_read_bytes_result, sosix_file_atomic_write, sosix_dir_create_all}
use std.nogc_sync_mut.io.file_ops.{secure_temp_dir}
use std.nogc_sync_mut.io.dir_ops.{dir_remove_all}

fn event_log_first_record() -> ReplayEntry:
    ReplayEntry(
        event_id: 17, logical_time: 65537, thread_id: 41, process_id: 9001,
        cpu_id: 2, kind: 6, flags: 3,
        payload_a: 65791, payload_b: 4294967297, payload_c: 255,
        payload_d: 1099511627777, crc32: 12345
    )

fn event_log_second_record() -> ReplayEntry:
    ReplayEntry(
        event_id: 29, logical_time: 131075, thread_id: 53, process_id: 9002,
        cpu_id: 4, kind: 2, flags: 5,
        payload_a: 131329, payload_b: 8589934595, payload_c: 256,
        payload_d: 2199023255555, crc32: 23456
    )

fn event_log_two_records() -> EventLog:
    var log = EventLog.create(Arch.RISCV32)
    log.add_events([event_log_first_record(), event_log_second_record()])
    log

fn expect_event_log_record(actual: ReplayEntry, expected: ReplayEntry):
    expect(actual.event_id).to_equal(expected.event_id)
    expect(actual.logical_time).to_equal(expected.logical_time)
    expect(actual.thread_id).to_equal(expected.thread_id)
    expect(actual.process_id).to_equal(expected.process_id)
    expect(actual.cpu_id).to_equal(expected.cpu_id)
    expect(actual.kind).to_equal(expected.kind)
    expect(actual.flags).to_equal(expected.flags)
    expect(actual.payload_a).to_equal(expected.payload_a)
    expect(actual.payload_b).to_equal(expected.payload_b)
    expect(actual.payload_c).to_equal(expected.payload_c)
    expect(actual.payload_d).to_equal(expected.payload_d)
    expect(actual.crc32).to_equal(expected.crc32)

fn run_event_log_host_fixture(body: fn(text) -> Result<Nil, text>):
    match secure_temp_dir(".", "replay-event-log-owned"):
        case Ok(root):
            val outcome = body(root)
            val removed = dir_remove_all(root)
            match outcome:
                case Ok(_):
                    expect(removed).to_equal(true)
                case Err(message):
                    expect(removed).to_equal(true)
                    fail("event-log host fixture failed: {message}")
        case Err(message):
            fail("could not create owned event-log fixture: {message}")

fn event_log_roundtrip_fixture(root: text) -> Result<Nil, text>:
    write_event_log(root, event_log_two_records())?
    val bytes = sosix_file_read_bytes_result("{root}/events.bin")?
    expect(bytes.len()).to_equal(160)
    val restored = read_event_log(root)?
    expect(restored.header.target.arch.to_text()).to_equal("riscv32")
    expect(restored.header.event_count).to_equal(2)
    expect(restored.entries.len()).to_equal(2)
    if restored.entries.len() != 2:
        return Err("round-trip did not restore both records")
    expect_event_log_record(restored.entries[0], event_log_first_record())
    expect_event_log_record(restored.entries[1], event_log_second_record())
    Ok(nil)

fn event_log_empty_rewrite_fixture(root: text) -> Result<Nil, text>:
    write_event_log(root, event_log_two_records())?
    val before = sosix_file_read_bytes_result("{root}/events.bin")?
    expect(before.len()).to_equal(160)
    if before.len() != 160:
        return Err("nonempty rewrite prerequisite did not persist two records")
    # This failing scenario also qualifies the repaired binary read conversion.
    val populated = read_event_log(root)?
    expect(populated.entries.len()).to_equal(2)
    if populated.entries.len() != 2:
        return Err("nonempty rewrite prerequisite did not decode both records")
    expect_event_log_record(populated.entries[0], event_log_first_record())
    expect_event_log_record(populated.entries[1], event_log_second_record())
    val empty = EventLog.create(Arch.RISCV32)
    write_event_log(root, empty)?
    val after = sosix_file_read_bytes_result("{root}/events.bin")?
    expect(after.len()).to_equal(0)
    val restored = read_event_log(root)?
    expect(restored.entries.len()).to_equal(0)
    expect(restored.header.event_count).to_equal(0)
    expect(restored.header.target.arch.to_text()).to_equal("riscv32")
    Ok(nil)

fn event_log_missing_events_fixture(root: text) -> Result<Nil, text>:
    val empty = EventLog.create(Arch.X86_64)
    if not sosix_file_atomic_write("{root}/manifest.sdn", empty.header.to_sdn()):
        return Err("could not create valid manifest for missing-events fixture")
    match read_event_log(root):
        case Err(message):
            expect(message).to_contain("events.bin")
            Ok(nil)
        case Ok(_):
            Err("missing events.bin was accepted as a valid empty trace")

fn event_log_blocked_events_fixture(root: text) -> Result<Nil, text>:
    if not sosix_dir_create_all("{root}/events.bin"):
        return Err("could not create blocking events.bin directory")
    val empty = EventLog.create(Arch.X86_64)
    match write_event_log(root, empty):
        case Err(message):
            expect(message).to_contain("events.bin")
            Ok(nil)
        case Ok(_):
            Err("empty event-log write accepted a directory as events.bin")

describe "Arch":
    it "X86_64 to_text":
        expect(Arch.X86_64.to_text()).to_equal("x86_64")

    it "RISCV32 to_text":
        expect(Arch.RISCV32.to_text()).to_equal("riscv32")

    it "ARM32 to_text":
        expect(Arch.ARM32.to_text()).to_equal("arm32")

    it "Arch.from_text riscv32":
        expect(Arch.from_text("riscv32").to_text()).to_equal("riscv32")

    it "Arch.from_text x86_64":
        expect(Arch.from_text("x86_64").to_text()).to_equal("x86_64")

    it "Arch.from_text amd64 maps to x86_64":
        expect(Arch.from_text("amd64").to_text()).to_equal("x86_64")

    it "X86_64 pointer_bits is 64":
        expect(Arch.X86_64.pointer_bits()).to_equal(64)

    it "RISCV32 pointer_bits is 32":
        expect(Arch.RISCV32.pointer_bits()).to_equal(32)

    it "ARM32 pointer_bits is 32":
        expect(Arch.ARM32.pointer_bits()).to_equal(32)

    it "RISCV64 pointer_bits is 64":
        expect(Arch.RISCV64.pointer_bits()).to_equal(64)

describe "TargetDesc":
    it "for_arch X86_64 has correct arch":
        val desc = TargetDesc.for_arch(Arch.X86_64)
        expect(desc.arch.to_text()).to_equal("x86_64")

    it "for_arch RISCV32 has correct arch":
        val desc = TargetDesc.for_arch(Arch.RISCV32)
        expect(desc.arch.to_text()).to_equal("riscv32")

    it "for_arch X86_64 has page_size 4096":
        val desc = TargetDesc.for_arch(Arch.X86_64)
        expect(desc.page_size).to_equal(4096)

    it "for_arch X86_64 has non-empty register_schema_id":
        val desc = TargetDesc.for_arch(Arch.X86_64)
        expect(desc.register_schema_id.len() > 0).to_equal(true)

describe "TraceHeader":
    it "create sets magic to SRPL":
        val desc = TargetDesc.for_arch(Arch.X86_64)
        val header = TraceHeader.create(desc)
        expect(header.magic).to_equal("SRPL")

    it "create sets version to 1":
        val desc = TargetDesc.for_arch(Arch.X86_64)
        val header = TraceHeader.create(desc)
        expect(header.version).to_equal(1)

    it "create sets event_count to 0":
        val desc = TargetDesc.for_arch(Arch.X86_64)
        val header = TraceHeader.create(desc)
        expect(header.event_count).to_equal(0)

    it "to_sdn contains SRPL magic":
        val desc = TargetDesc.for_arch(Arch.X86_64)
        val header = TraceHeader.create(desc)
        val sdn = header.to_sdn()
        expect(sdn).to_contain("SRPL")

    it "to_sdn contains arch name":
        val desc = TargetDesc.for_arch(Arch.X86_64)
        val header = TraceHeader.create(desc)
        val sdn = header.to_sdn()
        expect(sdn).to_contain("x86_64")

    it "to_sdn contains event_count stat":
        val desc = TargetDesc.for_arch(Arch.X86_64)
        val header = TraceHeader.create(desc)
        val sdn = header.to_sdn()
        expect(sdn).to_contain("event_count")

describe "EventLog":
    it "create sets initial event_count to 0":
        val log = EventLog.create(Arch.X86_64)
        expect(log.header.event_count).to_equal(0)

    it "add_event increments event_count":
        var log = EventLog.create(Arch.X86_64)
        val entry = ReplayEntry.create(EventKind.Schedule, 1, 1, 0)
        log.add_event(entry)
        expect(log.header.event_count).to_equal(1)

    it "add_event multiple times — count matches":
        var log = EventLog.create(Arch.RISCV32)
        val e0 = ReplayEntry.create(EventKind.TimerRead, 0, 1, 0)
        val e1 = ReplayEntry.create(EventKind.TimerRead, 1, 1, 0)
        val e2 = ReplayEntry.create(EventKind.TimerRead, 2, 1, 0)
        val e3 = ReplayEntry.create(EventKind.TimerRead, 3, 1, 0)
        log.add_event(e0)
        log.add_event(e1)
        log.add_event(e2)
        log.add_event(e3)
        expect(log.header.event_count).to_equal(4)

    it "entries.len matches header.event_count after add_event":
        var log = EventLog.create(Arch.X86_64)
        val e0 = ReplayEntry.create(EventKind.SyscallEnter, 1, 1, 0)
        val e1 = ReplayEntry.create(EventKind.SyscallExit, 2, 1, 0)
        log.add_event(e0)
        log.add_event(e1)
        expect(log.entries.len()).to_equal(log.header.event_count)

    it "add_events batch sets count correctly":
        var log = EventLog.create(Arch.ARM32)
        val e0 = ReplayEntry.create(EventKind.Schedule, 1, 1, 0)
        val e1 = ReplayEntry.create(EventKind.SyscallEnter, 2, 1, 0)
        val e2 = ReplayEntry.create(EventKind.SyscallExit, 3, 1, 0)
        log.add_events([e0, e1, e2])
        expect(log.header.event_count).to_equal(3)

    it "header arch matches create argument":
        val log = EventLog.create(Arch.RISCV32)
        expect(log.header.target.arch.to_text()).to_equal("riscv32")

describe "EventLog real host persistence":
    it "should round-trip every field of two distinct records in order":
        step("Write two production records to an owned directory and read their actual bytes and fields")
        run_event_log_host_fixture(event_log_roundtrip_fixture)

    it "should truncate existing event bytes when rewriting an empty log":
        step("Persist two records then replace them with an empty log and inspect the stored file")
        run_event_log_host_fixture(event_log_empty_rewrite_fixture)

    it "should reject missing events even when a valid manifest exists":
        step("Create only a real manifest and require the production reader to reject missing events.bin")
        run_event_log_host_fixture(event_log_missing_events_fixture)

    it "should report an empty-log write failure when events.bin is a directory":
        step("Create a real blocking directory and require the production writer to report failure")
        run_event_log_host_fixture(event_log_blocked_events_fixture)
```

</details>
