# replay_test_runner_adapter_spec

> @cover src/lib/nogc_sync_mut/replay/adapters/test_runner_replay.spl 60%

<!-- sdn-diagram:id=replay_test_runner_adapter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_test_runner_adapter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_test_runner_adapter_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_test_runner_adapter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# replay_test_runner_adapter_spec

@cover src/lib/nogc_sync_mut/replay/adapters/test_runner_replay.spl 60%

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #REPLAY-TESTRUN-001 to #REPLAY-TESTRUN-005 |
| Category | System / Replay Adapters |
| Status | Active |
| Source | `test/03_system/tools/replay_test_runner_adapter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

@cover src/lib/nogc_sync_mut/replay/adapters/test_runner_replay.spl 60%
System tests for the TestRunnerReplayAdapter layer.

Verifies mode enum, adapter creation, trace directory field,
and recorded-traces listing.

## Scenarios

### TestRunnerReplayAdapter

### TestReplayMode

#### Off mode to_text returns off

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = TestReplayMode::Off
expect(m.to_text()).to_equal("off")
```

</details>

#### RecordOnFail mode to_text returns record_on_fail

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = TestReplayMode::RecordOnFail
expect(m.to_text()).to_equal("record_on_fail")
```

</details>

### TestRunnerReplayAdapter lifecycle

#### create stores mode and trace_dir

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = TestRunnerReplayAdapter::create(TestReplayMode::Off, "/tmp/traces")
expect(adapter.mode.to_text()).to_equal("off")
expect(adapter.trace_dir).to_equal("/tmp/traces")
```

</details>

#### list_recorded_traces returns empty on fresh adapter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = TestRunnerReplayAdapter::create(TestReplayMode::Off, "/tmp/traces")
val traces = adapter.list_recorded_traces()
expect(traces.len()).to_equal(0)
```

</details>

#### get_trace_dir field returns configured path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = TestRunnerReplayAdapter::create(TestReplayMode::RecordOnFail, "/tmp/replay_traces")
expect(adapter.trace_dir).to_start_with("/tmp")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
