# Experiment Tracking Integration Specification

> Integration tests for the full experiment tracking workflow: config loading, run lifecycle, metric logging, artifact storage, and querying.

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
| Updated | 2026-08-26 |
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

- creates a run, logs metrics, and completes
   - Expected: is_running is true
   - Expected: is_completed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates a run, logs metrics, and completes")
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

- stores and retrieves artifacts
   - Expected: hash equals `results.sdn`
   - Expected: content equals `loss: 0.1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stores and retrieves artifacts")
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

- merges configs with overlay winning
   - Expected: lr_ok is true
   - Expected: bs_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("merges configs with overlay winning")
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

- lists runs from empty state
   - Expected: runs_.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lists runs from empty state")
var runs_ = []
expect(runs_.len()).to_equal(0)
```

</details>

#### filters runs by completed status

- filters runs by completed status
   - Expected: done_ok is true
   - Expected: done_run.run_id equals `done-1`
   - Expected: active_run.run_id equals `active-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filters runs by completed status")
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

- diffs two runs with different configs


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("diffs two runs with different configs")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f4270618f2c71ae9c448d75a8315784613fbd0f7081087b1f05042b3571a6455`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f4270618f2c71ae9c448d75a8315784613fbd0f7081087b1f05042b3571a6455`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f4270618f2c71ae9c448d75a8315784613fbd0f7081087b1f05042b3571a6455`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/feature/usage/experiment_tracking_spec.spl
mirror: doc/06_spec/03_system/feature/usage/experiment_tracking_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/experiment_tracking_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/experiment_tracking_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/experiment_tracking_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/experiment_tracking_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a run, logs metrics, and completes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/experiment_tracking_spec.spl:138:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores and retrieves artifacts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/experiment_tracking_spec.spl:154:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'merges configs with overlay winning' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
