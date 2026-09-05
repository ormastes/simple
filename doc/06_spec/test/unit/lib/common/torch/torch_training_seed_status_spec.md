# Torch Training Seed Status Specification

> <details>

<!-- sdn-diagram:id=torch_training_seed_status_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=torch_training_seed_status_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

torch_training_seed_status_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=torch_training_seed_status_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Torch Training Seed Status Specification

## Scenarios

### Torch training seed status

#### makes GC async seed helpers explicitly unsupported

- assert seed status surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_seed_status_surface("src/lib/gc_async_mut/torch/torch_training.spl")
```

</details>

#### makes NoGC async seed helpers explicitly unsupported

- assert seed status surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_seed_status_surface("src/lib/nogc_async_mut/torch/torch_training.spl")
```

</details>

#### makes NoGC sync seed helpers explicitly unsupported

- assert seed status surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_seed_status_surface("src/lib/nogc_sync_mut/torch/torch_training.spl")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/torch/torch_training_seed_status_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Torch training seed status

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
