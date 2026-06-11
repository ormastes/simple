# Replay Core Facade Specification

> <details>

<!-- sdn-diagram:id=replay_core_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_core_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_core_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_core_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Core Facade Specification

## Scenarios

### gc_async_mut replay core facades

#### re-exports event kind and event records

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = ReplayEvent(
    seq_id: 1,
    kind: ReplayEventKind.Step,
    timestamp: 2,
    file_hash: 3,
    line: 4,
    name_hash: 5,
    value_a: 6,
    value_b: 7
)

expect(event.kind.to_i32()).to_equal(2)
expect(ReplayEventKind.from_i32(2).to_text()).to_equal("Step")
```

</details>

#### re-exports replay engine and no-op hook

1. var engine = ReplayEngine create
2. engine on step
   - Expected: engine.events.len() equals `1`
   - Expected: engine.is_recording() is true
   - Expected: hook.is_off() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = ReplayEngine.create("record")
engine.on_step("main.spl", 12, 1)
val hook = NoopReplayHook()

expect(engine.events.len()).to_equal(1)
expect(engine.is_recording()).to_equal(true)
expect(hook.is_off()).to_equal(true)
```

</details>

#### re-exports global engine helpers

1. replay init
2. replay shutdown
   - Expected: active.is_some() is true
   - Expected: replay_get() equals `None`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
replay_init("record")
val active = replay_get()
replay_shutdown()

expect(active.is_some()).to_equal(true)
expect(replay_get()).to_equal(None)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/replay/core/replay_core_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut replay core facades

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
