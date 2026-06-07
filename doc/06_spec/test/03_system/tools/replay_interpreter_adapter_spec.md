# replay_interpreter_adapter_spec

> @cover src/lib/nogc_sync_mut/replay/adapters/interpreter_replay.spl 60%

<!-- sdn-diagram:id=replay_interpreter_adapter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_interpreter_adapter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_interpreter_adapter_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_interpreter_adapter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# replay_interpreter_adapter_spec

@cover src/lib/nogc_sync_mut/replay/adapters/interpreter_replay.spl 60%

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #REPLAY-INTERP-001 to #REPLAY-INTERP-006 |
| Category | System / Replay Adapters |
| Status | Active |
| Source | `test/03_system/tools/replay_interpreter_adapter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

@cover src/lib/nogc_sync_mut/replay/adapters/interpreter_replay.spl 60%
@cover src/lib/nogc_sync_mut/replay/adapters/interpreter_replay_event.spl 60%
System tests for the InterpreterReplayAdapter layer.

Verifies enum round-trips, struct construction, and adapter lifecycle
(create, event recording, checkpoint management).

## Scenarios

### InterpreterReplayAdapter

### InterpreterReplayEventKind

#### round-trips Step via to_i32 and from_i32

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = InterpreterReplayEventKind::Step
val v = k.to_i32()
val k2 = InterpreterReplayEventKind::from_i32(v)
expect(k2.to_i32()).to_equal(0)
```

</details>

#### to_text returns expected label

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = InterpreterReplayEventKind::Step
expect(k.to_text()).to_equal("Step")
```

</details>

### InterpreterReplayEvent creation

#### creates event with expected fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = InterpreterReplayEvent {
    seq_id: 7,
    kind: InterpreterReplayEventKind::FunctionCall,
    file: "main.spl",
    line: 42,
    name: "foo",
    value: "bar",
    timestamp: 100,
}
expect(ev.seq_id).to_equal(7)
expect(ev.line).to_equal(42)
expect(ev.file).to_equal("main.spl")
expect(ev.name).to_equal("foo")
expect(ev.value).to_equal("bar")
```

</details>

### InterpreterReplayAdapter lifecycle

#### create off mode has zero events

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = InterpreterReplayAdapter::create("off")
expect(adapter.event_count()).to_equal(0)
```

</details>

#### create record mode stores mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = InterpreterReplayAdapter::create("record")
expect(adapter.mode).to_equal("record")
```

</details>

#### save_checkpoint returns id >= 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = InterpreterReplayAdapter::create("record")
val id = adapter.save_checkpoint()
expect(id).to_be_greater_than(-1)
```

</details>

#### multiple checkpoints get sequential ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = InterpreterReplayAdapter::create("record")
val id0 = adapter.save_checkpoint()
val id1 = adapter.save_checkpoint()
val id2 = adapter.save_checkpoint()
expect(id0).to_equal(0)
expect(id1).to_equal(1)
expect(id2).to_equal(2)
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
