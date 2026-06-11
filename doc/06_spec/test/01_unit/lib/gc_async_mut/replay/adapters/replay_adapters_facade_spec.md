# Replay Adapters Facade Specification

> 1. var interp = InterpreterReplayAdapter create

<!-- sdn-diagram:id=replay_adapters_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_adapters_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_adapters_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_adapters_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Adapters Facade Specification

## Scenarios

### gc_async_mut replay adapter facades

#### re-exports interpreter and JIT adapters

1. var interp = InterpreterReplayAdapter create
2. interp wrap step
3. var jit = JitReplayAdapter create
4. jit on jit compile
   - Expected: InterpreterReplayEventKind.Step.to_i32() equals `0`
   - Expected: interp.event_count() equals `1`
   - Expected: jit.event_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interp = InterpreterReplayAdapter.create("record")
interp.wrap_step()

var jit = JitReplayAdapter.create(JitReplayMode.Record, "/tmp/simple-jit-replay")
jit.on_jit_compile("main", "module")

expect(InterpreterReplayEventKind.Step.to_i32()).to_equal(0)
expect(interp.event_count()).to_equal(1)
expect(jit.event_count()).to_equal(1)
```

</details>

#### re-exports remote and test runner adapters

1. var remote = RemoteReplayAdapter create
2. remote on register read
3. var runner = TestRunnerReplayAdapter create
4. runner wrap test execution
   - Expected: remote.event_count() equals `1`
   - Expected: runner.list_recorded_traces().len() equals `1`
   - Expected: TestReplayMode.from_text("replay").to_text() equals `replay`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var remote = RemoteReplayAdapter.create(RemoteReplayMode.Record)
remote.on_register_read("pc", 12)

var runner = TestRunnerReplayAdapter.create(TestReplayMode.RecordAlways, "/tmp/simple-test-replay")
runner.wrap_test_execution("sample_spec.spl", "default")

expect(remote.event_count()).to_equal(1)
expect(runner.list_recorded_traces().len()).to_equal(1)
expect(TestReplayMode.from_text("replay").to_text()).to_equal("replay")
```

</details>

#### re-exports hosted execution and QEMU adapter constructors

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hook = ExecutionReplayHook.create("/tmp/simple-exec-replay")
val qemu = QemuReplayAdapter.create_from_backend("/tmp/qmp.sock", 1234)

expect(hook.recording).to_equal(false)
expect(qemu.status()).to_equal("off")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/replay/adapters/replay_adapters_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut replay adapter facades

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
