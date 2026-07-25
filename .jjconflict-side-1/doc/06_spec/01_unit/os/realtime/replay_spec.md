# Replay Specification

> <details>

<!-- sdn-diagram:id=replay_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Specification

## Scenarios

### Replay mode constants

#### OFF=0 RECORD=1 REPLAY=2 VERIFY=3 CHAOS=4

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(RTOS_REPLAY_OFF).to_equal(0)
expect(RTOS_REPLAY_RECORD).to_equal(1)
expect(RTOS_REPLAY_REPLAY).to_equal(2)
expect(RTOS_REPLAY_VERIFY).to_equal(3)
expect(RTOS_REPLAY_CHAOS).to_equal(4)
```

</details>

### Replay mode predicates

#### is_recording true for RECORD and CHAOS

1. rtos replay set mode
   - Expected: rtos_replay_is_recording() is true
2. rtos replay set mode
   - Expected: rtos_replay_is_recording() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rtos_replay_set_mode(RTOS_REPLAY_RECORD)
expect(rtos_replay_is_recording()).to_equal(true)
rtos_replay_set_mode(RTOS_REPLAY_CHAOS)
expect(rtos_replay_is_recording()).to_equal(true)
```

</details>

#### is_replaying true for REPLAY, false for RECORD

1. rtos replay set mode
   - Expected: rtos_replay_is_replaying() is true
2. rtos replay set mode
   - Expected: rtos_replay_is_replaying() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rtos_replay_set_mode(RTOS_REPLAY_REPLAY)
expect(rtos_replay_is_replaying()).to_equal(true)
rtos_replay_set_mode(RTOS_REPLAY_RECORD)
expect(rtos_replay_is_replaying()).to_equal(false)
```

</details>

#### is_verifying true for VERIFY

1. rtos replay set mode
   - Expected: rtos_replay_is_verifying() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rtos_replay_set_mode(RTOS_REPLAY_VERIFY)
expect(rtos_replay_is_verifying()).to_equal(true)
```

</details>

#### is_off true for OFF

1. rtos replay set mode
   - Expected: rtos_replay_is_off() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rtos_replay_set_mode(RTOS_REPLAY_OFF)
expect(rtos_replay_is_off()).to_equal(true)
```

</details>

### Replay mode text

#### maps each mode to correct string

1. rtos replay set mode
   - Expected: rtos_replay_mode_text() equals `off`
2. rtos replay set mode
   - Expected: rtos_replay_mode_text() equals `record`
3. rtos replay set mode
   - Expected: rtos_replay_mode_text() equals `chaos-record`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rtos_replay_set_mode(RTOS_REPLAY_OFF)
expect(rtos_replay_mode_text()).to_equal("off")
rtos_replay_set_mode(RTOS_REPLAY_RECORD)
expect(rtos_replay_mode_text()).to_equal("record")
rtos_replay_set_mode(RTOS_REPLAY_CHAOS)
expect(rtos_replay_mode_text()).to_equal("chaos-record")
```

</details>

### RtosCheckpoint

#### constructs with all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cp = RtosCheckpoint(id: 1, tick: 500, current_task: 3, priority_bitmap: 15, rng_s0: 42, rng_s1: 99)
expect(cp.id).to_equal(1)
expect(cp.tick).to_equal(500)
expect(cp.current_task).to_equal(3)
expect(cp.rng_s0).to_equal(42)
```

</details>

#### find by id in single-element array

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cp = RtosCheckpoint(id: 7, tick: 1000, current_task: 0, priority_bitmap: 3, rng_s0: 10, rng_s1: 20)
val arr: [RtosCheckpoint] = [cp]
expect(checkpoint_find(arr, 7)).to_equal(0)
expect(arr[0].tick).to_equal(1000)
```

</details>

#### find returns -1 for missing id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [RtosCheckpoint] = []
expect(checkpoint_find(empty, 99)).to_equal(-1)
```

</details>

#### find returns correct index in multi-element array

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cp1 = RtosCheckpoint(id: 1, tick: 10, current_task: 0, priority_bitmap: 0, rng_s0: 0, rng_s1: 0)
val cp2 = RtosCheckpoint(id: 2, tick: 20, current_task: 0, priority_bitmap: 0, rng_s0: 0, rng_s1: 0)
val arr: [RtosCheckpoint] = [cp1, cp2]
expect(arr.len()).to_equal(2)
expect(checkpoint_find(arr, 2)).to_equal(1)
expect(checkpoint_find(arr, 99)).to_equal(-1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/realtime/replay_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Replay mode constants
- Replay mode predicates
- Replay mode text
- RtosCheckpoint

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
