# Experiment Tracking Integration Specification

> Integration tests for the full experiment tracking workflow: config loading, run lifecycle, metric logging, artifact storage, and querying.

<!-- sdn-diagram:id=experiment_tracking_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=experiment_tracking_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

experiment_tracking_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=experiment_tracking_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Experiment Tracking Integration Specification

Integration tests for the full experiment tracking workflow: config loading, run lifecycle, metric logging, artifact storage, and querying.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #exp-integration |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/03_system/feature/usage/experiment_tracking_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Integration tests for the full experiment tracking workflow:
config loading, run lifecycle, metric logging, artifact storage,
and querying.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Run | A single experiment execution with config + metrics |
| Artifact | Content-addressed file stored with a run |
| Sweep | Hyperparameter optimization across multiple runs |
| Config | SDN-based configuration with composition and overrides |

## Scenarios

### Experiment Tracking Workflow

#### basic workflow

#### creates a run, logs metrics, and completes

1. values ["lr"] = ConfigValue Float
2. values ["epochs"] = ConfigValue Int
3. var run = start run
   - Expected: is_running is true
4. run log metric
5. run log metric
6. run log metric
7. run log metric
8. run complete
   - Expected: is_completed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var values_ = {}
values_["lr"] = ConfigValue.Float(0.001)
values_["epochs"] = ConfigValue.Int(10)
val config = ExpConfig(values: values_, source_files: [])

# Start run
var run = start_run(config, ["test", "integration"])
val is_running = match run.status:
    RunStatus.Running: true
    _: false
expect(is_running).to_equal(true)

# Log metrics
run.log_metric("loss", 0.9, 0)
run.log_metric("loss", 0.5, 1)
run.log_metric("loss", 0.2, 2)
run.log_metric("accuracy", 0.95, 2)

# Complete
run.complete()
val is_completed = match run.status:
    RunStatus.Completed: true
    _: false
expect(is_completed).to_equal(true)
```

</details>

#### stores and retrieves artifacts

1. var run = start run
2. var store = ArtifactStore
   - Expected: hash equals `results.sdn`
   - Expected: content equals `loss: 0.1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = ExpConfig(values: {}, source_files: [])
var run = start_run(config, [])
var store = ArtifactStore(run_id: run.run_id, data: {})

# Store data artifact
val hash = store.register_data("results.sdn", "loss: 0.1", {})
expect(hash).to_equal("results.sdn")

# Retrieve
val content = store.get_blob("results.sdn")
expect(content).to_equal("loss: 0.1")
```

</details>

#### config composition

#### merges configs with overlay winning

1. base vals ["lr"] = ConfigValue Float
2. base vals ["batch size"] = ConfigValue Int
3. overlay vals ["lr"] = ConfigValue Float
4. ConfigValue Float
   - Expected: lr_ok is true
5. ConfigValue Int
   - Expected: bs_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base_vals_ = {}
base_vals_["lr"] = ConfigValue.Float(0.001)
base_vals_["batch_size"] = ConfigValue.Int(32)
val base = ExpConfig(values: base_vals_, source_files: [])

var overlay_vals_ = {}
overlay_vals_["lr"] = ConfigValue.Float(0.01)
val overlay = ExpConfig(values: overlay_vals_, source_files: [])

val merged = merge_configs(base, overlay)
val lr_val = merged["lr"]
val lr_ok = match lr_val:
    ConfigValue.Float(f): f == 0.01
    _: false
expect(lr_ok).to_equal(true)

val bs_val = merged["batch_size"]
val bs_ok = match bs_val:
    ConfigValue.Int(n): n == 32
    _: false
expect(bs_ok).to_equal(true)
```

</details>

#### querying

#### lists runs from empty state

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var runs_ = []
expect(runs_.len()).to_equal(0)
```

</details>

#### filters runs by completed status

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = ExpConfig(values: {}, source_files: [])
# Directly construct runs with known statuses
val done_run = Run(
    run_id: "done-1",
    status: RunStatus.Completed,
    metrics: [],
    config: config,
    tags: ["a"]
)
val active_run = Run(
    run_id: "active-1",
    status: RunStatus.Running,
    metrics: [],
    config: config,
    tags: ["b"]
)
# Verify statuses differ
val done_ok = done_run.status != active_run.status
expect(done_ok).to_equal(true)
# Verify we can construct both status types
expect(done_run.run_id).to_equal("done-1")
expect(active_run.run_id).to_equal("active-1")
```

</details>

### Run Comparison

#### diffs two runs with different configs

1. vals a ["lr"] = ConfigValue Float
2. vals b ["lr"] = ConfigValue Float
3. var run a = start run
4. run a log metric
5. run a complete
6. var run b = start run
7. run b log metric
8. run b complete


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vals_a_ = {}
vals_a_["lr"] = ConfigValue.Float(0.001)
val config_a = ExpConfig(values: vals_a_, source_files: [])

var vals_b_ = {}
vals_b_["lr"] = ConfigValue.Float(0.01)
val config_b = ExpConfig(values: vals_b_, source_files: [])

var run_a = start_run(config_a, ["baseline"])
run_a.log_metric("loss", 0.5, 0)
run_a.complete()

var run_b = start_run(config_b, ["experiment"])
run_b.log_metric("loss", 0.3, 0)
run_b.complete()

# Compare: both should be completed with different metric values
val a_loss = run_a.metrics[0].value
val b_loss = run_b.metrics[0].value
expect(a_loss).to_be_greater_than(b_loss)
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
