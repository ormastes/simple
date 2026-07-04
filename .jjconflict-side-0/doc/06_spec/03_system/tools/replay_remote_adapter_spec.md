# replay_remote_adapter_spec

> @cover src/lib/nogc_sync_mut/replay/adapters/remote_replay.spl 60%

<!-- sdn-diagram:id=replay_remote_adapter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_remote_adapter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_remote_adapter_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_remote_adapter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# replay_remote_adapter_spec

@cover src/lib/nogc_sync_mut/replay/adapters/remote_replay.spl 60%

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #REPLAY-REMOTE-001 to #REPLAY-REMOTE-005 |
| Category | System / Replay Adapters |
| Status | Active |
| Source | `test/03_system/tools/replay_remote_adapter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

@cover src/lib/nogc_sync_mut/replay/adapters/remote_replay.spl 60%
System tests for the RemoteReplayAdapter layer.

Verifies mode enum, adapter creation, event recording via on_register_read
and on_step_complete, and event counting.

## Scenarios

### RemoteReplayAdapter

### RemoteReplayMode

#### Off mode to_text returns off

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = RemoteReplayMode::Off
expect(m.to_text()).to_equal("off")
```

</details>

#### Record mode to_text returns record

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = RemoteReplayMode::Record
expect(m.to_text()).to_equal("record")
```

</details>

### RemoteReplayAdapter lifecycle

#### create Off mode has zero events

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = RemoteReplayAdapter::create(RemoteReplayMode::Off)
expect(adapter.event_count()).to_equal(0)
```

</details>

#### create Record mode stores mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = RemoteReplayAdapter::create(RemoteReplayMode::Record)
expect(adapter.mode.to_text()).to_equal("record")
```

</details>

#### on_register_read in Record mode logs one event

1. adapter on register read
   - Expected: adapter.event_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = RemoteReplayAdapter::create(RemoteReplayMode::Record)
adapter.on_register_read("pc", 0x1000)
expect(adapter.event_count()).to_equal(1)
```

</details>

#### on_step_complete in Record mode logs event

1. adapter on step complete
   - Expected: adapter.event_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = RemoteReplayAdapter::create(RemoteReplayMode::Record)
adapter.on_step_complete(0x2000, "main.spl", 10)
expect(adapter.event_count()).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
