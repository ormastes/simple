# Replay Remaining Facade Specification

> Tests covering gc_async_mut remaining replay facades.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Remaining Facade Specification

## Scenarios

### gc_async_mut remaining replay facades

#### re-exports event log and trace format helpers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports event log and trace format helpers
   - Expected: header.magic equals `SRPL`
   - Expected: log.header.target.arch.to_text() equals `x86_64`
   - Expected: manifest.pointer_bits equals `64`
   - Expected: index.lookup(7).len() equals `1`
   - Expected: package.event_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports event log and trace format helpers")
val target = TargetDesc.for_arch(Arch.X86_64)
val header = TraceHeader.create(target)
val log = EventLog.create(Arch.X86_64)
val manifest = TraceManifest.create("x86_64", "process")
var index = TraceIndex.create()
index.add(TraceIndexEntry.create(7, 8, "source_line"))
val package = TracePackage.create("/tmp/simple-trace", "process", "x86_64")

expect(header.magic).to_equal("SRPL")
expect(log.header.target.arch.to_text()).to_equal("x86_64")
expect(manifest.pointer_bits).to_equal(64)
expect(index.lookup(7).len()).to_equal(1)
expect(package.event_count()).to_equal(0)
```

</details>

#### re-exports integrated replay sessions

- re-exports integrated replay sessions
   - Expected: session.is_track_enabled(ReplayTrack.ProcessRR) is true
   - Expected: session.track_count() equals `1`
   - Expected: started.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports integrated replay sessions")
var session = IntegratedSession.create("s1", "/tmp/simple-trace")
session.enable_track(ReplayTrack.ProcessRR)
val started = session.start_recording()

expect(session.is_track_enabled(ReplayTrack.ProcessRR)).to_equal(true)
expect(session.track_count()).to_equal(1)
expect(started.is_ok()).to_equal(true)
expect(session.status()).to_contain("ProcessRR")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/replay/replay_remaining_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut remaining replay facades.
- gc_async_mut remaining replay facades

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `b30aecb8deaf4939b94b3b55285bd2f4d0158797cf141b02a828218e218d0c93`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b30aecb8deaf4939b94b3b55285bd2f4d0158797cf141b02a828218e218d0c93`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b30aecb8deaf4939b94b3b55285bd2f4d0158797cf141b02a828218e218d0c93`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/gc_async_mut/replay/replay_remaining_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/replay/replay_remaining_facade_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/replay/replay_remaining_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/replay/replay_remaining_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/replay/replay_remaining_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/replay/replay_remaining_facade_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports event log and trace format helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/replay/replay_remaining_facade_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports integrated replay sessions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
