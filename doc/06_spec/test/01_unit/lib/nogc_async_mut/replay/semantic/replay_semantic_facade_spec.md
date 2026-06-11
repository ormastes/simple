# Replay Semantic Facade Specification

> <details>

<!-- sdn-diagram:id=replay_semantic_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_semantic_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_semantic_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_semantic_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Semantic Facade Specification

## Scenarios

### nogc_async_mut replay semantic facades

#### re-exports semantic event records

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = SemanticEvent.create(SemanticEventKind.VariableWrite)

expect(ev.kind).to_equal(SemanticEventKind.VariableWrite.to_i32())
expect(ev.event_kind().to_i32()).to_equal(SemanticEventKind.VariableWrite.to_i32())
expect(SEMANTIC_EVENT_SIZE).to_equal(68)
```

</details>

#### re-exports object registry and scenario correlator

1. var registry = ObjectRegistry create
2. var correlator = ScenarioCorrelator from scenario
3. correlator add step
   - Expected: obj_id equals `1`
   - Expected: registry.active_count() equals `1`
   - Expected: correlator.step_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var registry = ObjectRegistry.create()
val obj_id = registry.register(3, 4, 5)
var correlator = ScenarioCorrelator.from_scenario("checkout")
correlator.add_step("submit order", 1, 2)

expect(obj_id).to_equal(1)
expect(registry.active_count()).to_equal(1)
expect(correlator.step_count()).to_equal(1)
expect(correlator.summary()).to_contain("checkout")
```

</details>

#### re-exports trace writer and async timeline

1. var timeline = AsyncTaskTimeline create
2. timeline add entry
3. timeline add entry
   - Expected: writer.event_count equals `0`
   - Expected: timeline.is_complete() is true
   - Expected: timeline.duration() equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val writer = TraceWriter.create("/tmp/simple-semantic.sst", 1024)
var timeline = AsyncTaskTimeline.create(10, 20)
timeline.add_entry(1, 100, AsyncTaskState.Spawned)
timeline.add_entry(2, 150, AsyncTaskState.Completed)

expect(writer.event_count).to_equal(0)
expect(timeline.is_complete()).to_equal(true)
expect(timeline.duration()).to_equal(50)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/replay/semantic/replay_semantic_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut replay semantic facades

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
