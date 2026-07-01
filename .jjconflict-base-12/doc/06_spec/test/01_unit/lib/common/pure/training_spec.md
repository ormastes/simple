# Training Specification

> <details>

<!-- sdn-diagram:id=training_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=training_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

training_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=training_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Training Specification

## Scenarios

### Training

#### keeps loss and optimizer classes available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = torch_training_source()

expect(source).to_contain("class MSELoss:")
expect(source).to_contain("class CrossEntropyLoss:")
expect(source).to_contain("class SGD:")
expect(source).to_contain("class Adam:")
expect(source).to_contain("class RMSprop:")
```

</details>

#### keeps optimizer step and zero-grad operations available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = torch_training_source()

expect(source).to_contain("fn step():")
expect(source).to_contain("me step():")
expect(source).to_contain("fn zero_grad():")
expect(source).to_contain("rt_torch_autograd_grad(param.handle)")
```

</details>

#### keeps deterministic training utility functions available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = torch_training_source()

expect(source).to_contain("fn no_grad(f: fn()) -> void")
expect(source).to_contain("fn set_seed(seed: i64)")
expect(source).to_contain("fn manual_seed(seed: i64)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/pure/training_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Training

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
