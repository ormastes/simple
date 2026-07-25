# Replay Integration Specification

> <details>

<!-- sdn-diagram:id=replay_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_integration_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Integration Specification

## Scenarios

### IntegratedSession create

#### create sets session_id and trace_dir

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = IntegratedSession.create("sess-001", "/tmp/traces/sess-001")
expect(s.session_id).to_equal("sess-001")
expect(s.trace_dir).to_equal("/tmp/traces/sess-001")
```

</details>

#### create starts with no active tracks

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = IntegratedSession.create("sess-002", "/tmp/t")
expect(s.track_count()).to_equal(0)
```

</details>

#### create starts not recording and not replaying

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = IntegratedSession.create("sess-003", "/tmp/t")
expect(s.recording).to_equal(false)
expect(s.replaying).to_equal(false)
```

</details>

### IntegratedSession enable_track and disable_track

#### enable_track adds a track

1. var s = IntegratedSession create
2. s enable track
   - Expected: s.track_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = IntegratedSession.create("sess-004", "/tmp/t")
s.enable_track(ReplayTrack.QEMU)
expect(s.track_count()).to_equal(1)
```

</details>

#### enable_track is idempotent

1. var s = IntegratedSession create
2. s enable track
3. s enable track
   - Expected: s.track_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = IntegratedSession.create("sess-005", "/tmp/t")
s.enable_track(ReplayTrack.ProcessRR)
s.enable_track(ReplayTrack.ProcessRR)
expect(s.track_count()).to_equal(1)
```

</details>

#### enable_track multiple distinct tracks

1. var s = IntegratedSession create
2. s enable track
3. s enable track
4. s enable track
   - Expected: s.track_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = IntegratedSession.create("sess-006", "/tmp/t")
s.enable_track(ReplayTrack.QEMU)
s.enable_track(ReplayTrack.SemanticTrace)
s.enable_track(ReplayTrack.VmReplay)
expect(s.track_count()).to_equal(3)
```

</details>

#### disable_track removes a track

1. var s = IntegratedSession create
2. s enable track
3. s enable track
4. s disable track
   - Expected: s.track_count() equals `1`
   - Expected: s.is_track_enabled(ReplayTrack.QEMU) is false
   - Expected: s.is_track_enabled(ReplayTrack.KernelEventLog) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = IntegratedSession.create("sess-007", "/tmp/t")
s.enable_track(ReplayTrack.QEMU)
s.enable_track(ReplayTrack.KernelEventLog)
s.disable_track(ReplayTrack.QEMU)
expect(s.track_count()).to_equal(1)
expect(s.is_track_enabled(ReplayTrack.QEMU)).to_equal(false)
expect(s.is_track_enabled(ReplayTrack.KernelEventLog)).to_equal(true)
```

</details>

### IntegratedSession is_track_enabled

#### returns false when track is not active

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = IntegratedSession.create("sess-008", "/tmp/t")
expect(s.is_track_enabled(ReplayTrack.ContainerCheckpoint)).to_equal(false)
```

</details>

#### returns true after enabling a track

1. var s = IntegratedSession create
2. s enable track
   - Expected: s.is_track_enabled(ReplayTrack.SemanticTrace) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = IntegratedSession.create("sess-009", "/tmp/t")
s.enable_track(ReplayTrack.SemanticTrace)
expect(s.is_track_enabled(ReplayTrack.SemanticTrace)).to_equal(true)
```

</details>

### IntegratedSession start_recording and stop_recording

#### start_recording sets recording flag

1. var s = IntegratedSession create
2. s enable track
   - Expected: s.recording is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = IntegratedSession.create("sess-010", "/tmp/t")
s.enable_track(ReplayTrack.QEMU)
val r = s.start_recording()
expect(s.recording).to_equal(true)
```

</details>

#### stop_recording clears recording flag

1. var s = IntegratedSession create
2. s enable track
3. s start recording
   - Expected: s.recording is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = IntegratedSession.create("sess-011", "/tmp/t")
s.enable_track(ReplayTrack.QEMU)
s.start_recording()
val r = s.stop_recording()
expect(s.recording).to_equal(false)
```

</details>

### IntegratedSession start_replay and stop_replay

#### start_replay sets replaying flag

1. var s = IntegratedSession create
   - Expected: s.replaying is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = IntegratedSession.create("sess-012", "/tmp/t")
val r = s.start_replay()
expect(s.replaying).to_equal(true)
```

</details>

#### stop_replay clears replaying flag

1. var s = IntegratedSession create
2. s start replay
   - Expected: s.replaying is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = IntegratedSession.create("sess-013", "/tmp/t")
s.start_replay()
val r = s.stop_replay()
expect(s.replaying).to_equal(false)
```

</details>

### IntegratedSession status

#### status contains session_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = IntegratedSession.create("sess-014", "/tmp/t")
val out = s.status()
expect(out).to_contain("sess-014")
```

</details>

#### status contains trace_dir

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = IntegratedSession.create("sess-015", "/tmp/traces/x")
val out = s.status()
expect(out).to_contain("/tmp/traces/x")
```

</details>

#### status shows idle when not recording or replaying

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = IntegratedSession.create("sess-016", "/tmp/t")
val out = s.status()
expect(out).to_contain("idle")
```

</details>

### ReplayTrack to_i32 ordinals

#### QEMU is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ReplayTrack.QEMU.to_i32()).to_equal(0)
```

</details>

#### VmReplay is 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ReplayTrack.VmReplay.to_i32()).to_equal(5)
```

</details>

#### ContainerCheckpoint is 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ReplayTrack.ContainerCheckpoint.to_i32()).to_equal(4)
```

</details>

### ReplayTrack to_text

#### QEMU to_text returns QEMU

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ReplayTrack.QEMU.to_text()).to_equal("QEMU")
```

</details>

#### SemanticTrace to_text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ReplayTrack.SemanticTrace.to_text()).to_equal("SemanticTrace")
```

</details>

#### KernelEventLog to_text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ReplayTrack.KernelEventLog.to_text()).to_equal("KernelEventLog")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- IntegratedSession create
- IntegratedSession enable_track and disable_track
- IntegratedSession is_track_enabled
- IntegratedSession start_recording and stop_recording
- IntegratedSession start_replay and stop_replay
- IntegratedSession status
- ReplayTrack to_i32 ordinals
- ReplayTrack to_text

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
