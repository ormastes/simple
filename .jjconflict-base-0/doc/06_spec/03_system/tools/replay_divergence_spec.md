# Replay Divergence Specification

> <details>

<!-- sdn-diagram:id=replay_divergence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_divergence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_divergence_spec -> std
replay_divergence_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_divergence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Divergence Specification

## Scenarios

### DivergenceKind to_i32 round-trip

#### ScheduleMismatch round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = DivergenceKind.ScheduleMismatch.to_i32()
expect(v).to_equal(0)
expect(DivergenceKind.from_i32(v).to_i32()).to_equal(0)
```

</details>

#### SyscallMismatch round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = DivergenceKind.SyscallMismatch.to_i32()
expect(v).to_equal(1)
expect(DivergenceKind.from_i32(v).to_i32()).to_equal(1)
```

</details>

#### IrqMismatch round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = DivergenceKind.IrqMismatch.to_i32()
expect(v).to_equal(2)
expect(DivergenceKind.from_i32(v).to_i32()).to_equal(2)
```

</details>

#### TimerMismatch round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = DivergenceKind.TimerMismatch.to_i32()
expect(v).to_equal(3)
expect(DivergenceKind.from_i32(v).to_i32()).to_equal(3)
```

</details>

#### RandomMismatch round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = DivergenceKind.RandomMismatch.to_i32()
expect(v).to_equal(4)
expect(DivergenceKind.from_i32(v).to_i32()).to_equal(4)
```

</details>

#### IpcMismatch round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = DivergenceKind.IpcMismatch.to_i32()
expect(v).to_equal(5)
expect(DivergenceKind.from_i32(v).to_i32()).to_equal(5)
```

</details>

#### ThreadMismatch round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = DivergenceKind.ThreadMismatch.to_i32()
expect(v).to_equal(6)
expect(DivergenceKind.from_i32(v).to_i32()).to_equal(6)
```

</details>

#### CheckpointMismatch round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = DivergenceKind.CheckpointMismatch.to_i32()
expect(v).to_equal(7)
expect(DivergenceKind.from_i32(v).to_i32()).to_equal(7)
```

</details>

### DivergenceKind to_text

#### ScheduleMismatch to_text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(DivergenceKind.ScheduleMismatch.to_text()).to_equal("schedule-mismatch")
```

</details>

#### SyscallMismatch to_text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(DivergenceKind.SyscallMismatch.to_text()).to_equal("syscall-mismatch")
```

</details>

#### IrqMismatch to_text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(DivergenceKind.IrqMismatch.to_text()).to_equal("irq-mismatch")
```

</details>

#### CheckpointMismatch to_text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(DivergenceKind.CheckpointMismatch.to_text()).to_equal("checkpoint-mismatch")
```

</details>

### DivergenceRecord

#### fields are accessible after construction

1. clear divergences
2. report divergence
   - Expected: r.event_id equals `42`
   - Expected: r.expected equals `100`
   - Expected: r.actual equals `200`
   - Expected: r.kind.to_i32() equals `DivergenceKind.ScheduleMismatch.to_i32()`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_divergences()
report_divergence(DivergenceKind.ScheduleMismatch, 42, 100, 200)
val rec = get_divergence(0)
match rec:
    case Some(r):
        expect(r.event_id).to_equal(42)
        expect(r.expected).to_equal(100)
        expect(r.actual).to_equal(200)
        expect(r.kind.to_i32()).to_equal(DivergenceKind.ScheduleMismatch.to_i32())
    case None:
        expect(false).to_equal(true)
```

</details>

### report_divergence

#### logs a single divergence

1. clear divergences
2. report divergence
   - Expected: get_divergence_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_divergences()
report_divergence(DivergenceKind.SyscallMismatch, 10, 50, 60)
expect(get_divergence_count()).to_equal(1)
```

</details>

#### records expected and actual values

1. clear divergences
2. report divergence
   - Expected: r.expected equals `300`
   - Expected: r.actual equals `400`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_divergences()
report_divergence(DivergenceKind.IrqMismatch, 7, 300, 400)
val rec = get_divergence(0)
match rec:
    case Some(r):
        expect(r.expected).to_equal(300)
        expect(r.actual).to_equal(400)
    case None:
        expect(false).to_equal(true)
```

</details>

### get_divergence_count

#### starts at zero after clear

1. clear divergences
   - Expected: get_divergence_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_divergences()
expect(get_divergence_count()).to_equal(0)
```

</details>

#### increments on each report

1. clear divergences
2. report divergence
   - Expected: get_divergence_count() equals `1`
3. report divergence
   - Expected: get_divergence_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_divergences()
report_divergence(DivergenceKind.TimerMismatch, 1, 10, 20)
expect(get_divergence_count()).to_equal(1)
report_divergence(DivergenceKind.RandomMismatch, 2, 30, 40)
expect(get_divergence_count()).to_equal(2)
```

</details>

### get_divergence

#### returns Some for valid index

1. clear divergences
2. report divergence
   - Expected: r.kind.to_i32() equals `DivergenceKind.IpcMismatch.to_i32()`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_divergences()
report_divergence(DivergenceKind.IpcMismatch, 5, 77, 88)
val rec = get_divergence(0)
match rec:
    case Some(r):
        expect(r.kind.to_i32()).to_equal(DivergenceKind.IpcMismatch.to_i32())
    case None:
        expect(false).to_equal(true)
```

</details>

#### returns None for out-of-bounds index

1. clear divergences
   - Expected: false is true
   - Expected: rec.is_none() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_divergences()
val rec = get_divergence(99)
match rec:
    case Some(r):
        expect(false).to_equal(true)
    case None:
        expect(rec.is_none()).to_equal(true)
```

</details>

#### returns None for negative index

1. clear divergences
   - Expected: false is true
   - Expected: rec.is_none() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_divergences()
val rec = get_divergence(-1)
match rec:
    case Some(r):
        expect(false).to_equal(true)
    case None:
        expect(rec.is_none()).to_equal(true)
```

</details>

### clear_divergences

#### resets count to zero

1. clear divergences
2. report divergence
3. report divergence
   - Expected: get_divergence_count() equals `2`
4. clear divergences
   - Expected: get_divergence_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_divergences()
report_divergence(DivergenceKind.ThreadMismatch, 1, 10, 20)
report_divergence(DivergenceKind.CheckpointMismatch, 2, 30, 40)
expect(get_divergence_count()).to_equal(2)
clear_divergences()
expect(get_divergence_count()).to_equal(0)
```

</details>

#### clears the log so get_divergence returns None

1. clear divergences
2. report divergence
3. clear divergences
   - Expected: false is true
   - Expected: rec.is_none() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_divergences()
report_divergence(DivergenceKind.ScheduleMismatch, 1, 5, 6)
clear_divergences()
val rec = get_divergence(0)
match rec:
    case Some(r):
        expect(false).to_equal(true)
    case None:
        expect(rec.is_none()).to_equal(true)
```

</details>

### has_diverged

#### returns false when no divergences reported

1. clear divergences
   - Expected: has_diverged() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_divergences()
expect(has_diverged()).to_equal(false)
```

</details>

#### returns true after a divergence is reported

1. clear divergences
2. report divergence
   - Expected: has_diverged() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_divergences()
report_divergence(DivergenceKind.SyscallMismatch, 1, 10, 20)
expect(has_diverged()).to_equal(true)
```

</details>

#### returns false after clear

1. clear divergences
2. report divergence
   - Expected: has_diverged() is true
3. clear divergences
   - Expected: has_diverged() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_divergences()
report_divergence(DivergenceKind.IrqMismatch, 1, 10, 20)
expect(has_diverged()).to_equal(true)
clear_divergences()
expect(has_diverged()).to_equal(false)
```

</details>

### multiple divergences

#### accumulate in order

1. clear divergences
2. report divergence
3. report divergence
4. report divergence
   - Expected: get_divergence_count() equals `3`
   - Expected: r.kind.to_i32() equals `DivergenceKind.ScheduleMismatch.to_i32()`
   - Expected: r.event_id equals `1`
   - Expected: false is true
   - Expected: r.kind.to_i32() equals `DivergenceKind.SyscallMismatch.to_i32()`
   - Expected: r.event_id equals `2`
   - Expected: false is true
   - Expected: r.kind.to_i32() equals `DivergenceKind.IrqMismatch.to_i32()`
   - Expected: r.event_id equals `3`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
clear_divergences()
report_divergence(DivergenceKind.ScheduleMismatch, 1, 10, 11)
report_divergence(DivergenceKind.SyscallMismatch, 2, 20, 22)
report_divergence(DivergenceKind.IrqMismatch, 3, 30, 33)
expect(get_divergence_count()).to_equal(3)

val first = get_divergence(0)
match first:
    case Some(r):
        expect(r.kind.to_i32()).to_equal(DivergenceKind.ScheduleMismatch.to_i32())
        expect(r.event_id).to_equal(1)
    case None:
        expect(false).to_equal(true)

val second = get_divergence(1)
match second:
    case Some(r):
        expect(r.kind.to_i32()).to_equal(DivergenceKind.SyscallMismatch.to_i32())
        expect(r.event_id).to_equal(2)
    case None:
        expect(false).to_equal(true)

val third = get_divergence(2)
match third:
    case Some(r):
        expect(r.kind.to_i32()).to_equal(DivergenceKind.IrqMismatch.to_i32())
        expect(r.event_id).to_equal(3)
    case None:
        expect(false).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_divergence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DivergenceKind to_i32 round-trip
- DivergenceKind to_text
- DivergenceRecord
- report_divergence
- get_divergence_count
- get_divergence
- clear_divergences
- has_diverged
- multiple divergences

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
