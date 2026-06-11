# Replay Remaining Facade Specification

> 1. var index = TraceIndex create

<!-- sdn-diagram:id=replay_remaining_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_remaining_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_remaining_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_remaining_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Remaining Facade Specification

## Scenarios

### nogc_async_mut remaining replay facades

#### re-exports event log and trace format helpers

1. var index = TraceIndex create
2. index add
   - Expected: header.magic equals `SRPL`
   - Expected: log.header.target.arch.to_text() equals `x86_64`
   - Expected: manifest.pointer_bits equals `64`
   - Expected: index.lookup(7).len() equals `1`
   - Expected: package.event_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var session = IntegratedSession create
2. session enable track
   - Expected: session.is_track_enabled(ReplayTrack.ProcessRR) is true
   - Expected: session.track_count() equals `1`
   - Expected: started.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/lib/nogc_async_mut/replay/replay_remaining_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut remaining replay facades

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
