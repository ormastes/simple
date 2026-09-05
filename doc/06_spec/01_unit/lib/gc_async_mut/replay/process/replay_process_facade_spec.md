# Replay Process Facade Specification

> Tests covering gc_async_mut replay process facades.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Process Facade Specification

## Scenarios

### gc_async_mut replay process facades

#### re-exports event records and metadata

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports event records and metadata
   - Expected: ev.kind equals `ProcessEventKind.SyscallEntry.to_i32()`
   - Expected: meta.command equals `echo hi`
   - Expected: PROCESS_EVENT_SIZE equals `60`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports event records and metadata")
val ev = ProcessReplayEvent.syscall_entry(1, 42, 99, 60, 3, 4)
val meta = ProcessTraceMetadata.create("echo hi")

expect(ev.kind).to_equal(ProcessEventKind.SyscallEntry.to_i32())
expect(ev.summary()).to_contain("syscall_entry")
expect(meta.command).to_equal("echo hi")
expect(PROCESS_EVENT_SIZE).to_equal(60)
```

</details>

#### re-exports recorder, replayer, and checkpoint types

- re-exports recorder, replayer, and checkpoint types
   - Expected: recorder.mode equals `RecordingMode.Idle`
   - Expected: replayer.event_count() equals `0`
   - Expected: checkpoint.get_register("pc") equals `Some(100)`
   - Expected: ReplayVerdict.Match.to_text() equals `match`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports recorder, replayer, and checkpoint types")
val recorder = ProcessRecorder.create("echo hi", "/tmp/simple-process-replay")
val replayer = ProcessReplayer.create("/tmp/simple-process-replay")
var checkpoint = PageCheckpoint.create(1, 10)
checkpoint.add_register("pc", 100)

expect(recorder.mode).to_equal(RecordingMode.Idle)
expect(replayer.event_count()).to_equal(0)
expect(checkpoint.get_register("pc")).to_equal(Some(100))
expect(ReplayVerdict.Match.to_text()).to_equal("match")
```

</details>

#### re-exports thread recorder and chaos scheduler

- re-exports thread recorder and chaos scheduler
   - Expected: threads.thread_count() equals `2`
   - Expected: threads.switch_count() equals `1`
   - Expected: chosen equals `11`
   - Expected: scheduler.schedule_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports thread recorder and chaos scheduler")
var threads = ThreadRecorder.create()
threads.on_thread_create(10, 11, 1)
threads.on_thread_switch(10, 11, 0, 2)

var scheduler = ChaosScheduler.create(ChaosStrategy.RoundRobin, 1)
val chosen = scheduler.pick_next([11, 12])

expect(threads.thread_count()).to_equal(2)
expect(threads.switch_count()).to_equal(1)
expect(chosen).to_equal(11)
expect(scheduler.schedule_count()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/replay/process/replay_process_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut replay process facades.
- gc_async_mut replay process facades

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `59a1dc7cca3290aa34896b5e7db6e38e252469c2bc85a64def298fc14d0b0855`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `59a1dc7cca3290aa34896b5e7db6e38e252469c2bc85a64def298fc14d0b0855`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `59a1dc7cca3290aa34896b5e7db6e38e252469c2bc85a64def298fc14d0b0855`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/replay/process/replay_process_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/replay/process/replay_process_facade_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/replay/process/replay_process_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/replay/process/replay_process_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/replay/process/replay_process_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/replay/process/replay_process_facade_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports event records and metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/replay/process/replay_process_facade_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports recorder, replayer, and checkpoint types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/replay/process/replay_process_facade_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports thread recorder and chaos scheduler' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
