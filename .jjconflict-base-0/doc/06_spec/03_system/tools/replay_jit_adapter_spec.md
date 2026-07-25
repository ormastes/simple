# replay_jit_adapter_spec

> @cover src/lib/nogc_sync_mut/replay/adapters/jit_replay.spl 60%

<!-- sdn-diagram:id=replay_jit_adapter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_jit_adapter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_jit_adapter_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_jit_adapter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# replay_jit_adapter_spec

@cover src/lib/nogc_sync_mut/replay/adapters/jit_replay.spl 60%

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #REPLAY-JIT-001 to #REPLAY-JIT-006 |
| Category | System / Replay Adapters |
| Status | Active |
| Source | `test/03_system/tools/replay_jit_adapter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

@cover src/lib/nogc_sync_mut/replay/adapters/jit_replay.spl 60%
@cover src/lib/nogc_sync_mut/replay/adapters/jit_replay_event.spl 60%
System tests for the JitReplayAdapter layer.

Verifies enum round-trips, event struct construction, adapter lifecycle,
on_jit_compile event recording, and checkpoint management.

## Scenarios

### JitReplayAdapter

### JitReplayEventKind

#### round-trips Compile via to_i32 and from_i32

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = JitReplayEventKind::Compile
val v = k.to_i32()
val k2 = JitReplayEventKind::from_i32(v)
expect(k2.to_i32()).to_equal(0)
```

</details>

#### to_text returns expected label

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = JitReplayEventKind::Compile
expect(k.to_text()).to_equal("Compile")
```

</details>

### JitReplayEvent creation

#### creates event with expected fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = JitReplayEvent {
    seq_id: 3,
    kind: JitReplayEventKind::Execute,
    function_hash: 111,
    module_hash: 222,
    args_hash: 333,
    result: 0,
    timestamp: 9999,
}
expect(ev.seq_id).to_equal(3)
expect(ev.function_hash).to_equal(111)
expect(ev.args_hash).to_equal(333)
```

</details>

### JitReplayAdapter lifecycle

#### create Off mode has zero events

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = JitReplayAdapter::create(JitReplayMode::Off, "")
expect(adapter.event_count()).to_equal(0)
```

</details>

#### create Record mode stores mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = JitReplayAdapter::create(JitReplayMode::Record, "/tmp/jit.trace")
expect(adapter.mode.to_text()).to_equal("record")
```

</details>

#### on_jit_compile in Record mode logs one event

1. adapter on jit compile
   - Expected: adapter.event_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = JitReplayAdapter::create(JitReplayMode::Record, "/tmp/jit.trace")
adapter.on_jit_compile("my_fn", "my_module")
expect(adapter.event_count()).to_equal(1)
```

</details>

#### save_checkpoint returns id >= 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = JitReplayAdapter::create(JitReplayMode::Record, "/tmp/jit.trace")
val id = adapter.save_checkpoint()
expect(id).to_be_greater_than(-1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
