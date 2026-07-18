# Sweep Specification

> <details>

<!-- sdn-diagram:id=sweep_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sweep_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sweep_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sweep_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sweep Specification

## Scenarios

### Trial

#### keeps common sweep trial sampler pruner and study APIs available

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = exp_source("sweep")

expect(source).to_contain("enum TrialStatus")
expect(source).to_contain("struct Trial")
expect(source).to_contain("me suggest_float(name: text, low: f64, high: f64) -> f64")
expect(source).to_contain("struct Sampler")
expect(source).to_contain("static fn random(seed: i64) -> Sampler")
expect(source).to_contain("struct Pruner")
expect(source).to_contain("struct Study")
expect(source).to_contain("me optimize(objective: fn(Trial) -> f64, n_trials: i64)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/exp/sweep_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Trial

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
