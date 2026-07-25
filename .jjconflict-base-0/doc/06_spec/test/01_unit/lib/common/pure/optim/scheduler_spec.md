# Scheduler Specification

> <details>

<!-- sdn-diagram:id=scheduler_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scheduler_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scheduler_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scheduler_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scheduler Specification

## Scenarios

### Scheduler

#### keeps linear warmup scheduler available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = torch_ops_source()

expect(source).to_contain("fn lr_warmup_linear(step: i64, warmup_steps: i64, total_steps: i64, base_lr: f64) -> f64")
expect(source).to_contain("return base_lr * step / warmup_steps")
expect(source).to_contain("val decay_steps = total_steps - warmup_steps")
expect(source).to_contain("base_lr * remaining / decay_steps")
```

</details>

#### keeps cosine warmup scheduler approximation available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = torch_ops_source()

expect(source).to_contain("fn lr_warmup_cosine(step: i64, warmup_steps: i64, total_steps: i64, base_lr: f64, min_lr: f64) -> f64")
expect(source).to_contain("val progress = (step - warmup_steps) * 1.0 / (total_steps - warmup_steps)")
expect(source).to_contain("val decay = 1.0 - progress")
expect(source).to_contain("min_lr + (base_lr - min_lr) * clamped")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/pure/optim/scheduler_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Scheduler

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
