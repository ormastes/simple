# Dict Config Specification

> Tests covering PyTorch Dict Configuration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dict Config Specification

## Scenarios

### PyTorch Dict Configuration

#### model configuration

#### creates model config dict

- creates model config dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates model config dict")
val config = {
    "input_size": 784,
    "hidden_size": 256,
    "output_size": 10,
    "dropout": 0.5
}
expect config["input_size"] == 784
expect config["hidden_size"] == 256
```

</details>

#### creates optimizer config

- creates optimizer config


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates optimizer config")
val opt_config = {
    "lr": 0.001,
    "momentum": 0.9,
    "weight_decay": 0.0001
}
expect opt_config["lr"] == 0.001
```

</details>

#### creates training config

- creates training config


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates training config")
val train_config = {
    "epochs": 100,
    "batch_size": 32,
    "learning_rate": 0.01,
    "shuffle": true
}
expect train_config["epochs"] == 100
expect train_config["shuffle"] == true
```

</details>

#### hyperparameters

#### stores hyperparameter dict

- stores hyperparameter dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores hyperparameter dict")
val hyperparams = {
    "learning_rate": 0.001,
    "beta1": 0.9,
    "beta2": 0.999,
    "epsilon": 1e-8
}
expect hyperparams["learning_rate"] == 0.001
```

</details>

#### creates nested config

- creates nested config


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates nested config")
val config = {
    "model": {
        "layers": [128, 64, 32],
        "activation": "relu"
    },
    "optimizer": {
        "type": "adam",
        "lr": 0.001
    }
}
expect config["model"]["activation"] == "relu"
expect config["optimizer"]["type"] == "adam"
```

</details>

#### device configuration

#### creates device config

- creates device config


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates device config")
val device_config = {
    "device": "cuda",
    "gpu_id": 0,
    "mixed_precision": true
}
expect device_config["device"] == "cuda"
expect device_config["gpu_id"] == 0
```

</details>

#### stores multiple device configs

- stores multiple device configs


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores multiple device configs")
val configs = {
    "training": {"device": "cuda", "gpu": 0},
    "inference": {"device": "cpu", "threads": 4}
}
expect configs["training"]["device"] == "cuda"
expect configs["inference"]["device"] == "cpu"
```

</details>

#### dataset configuration

#### creates dataset config

- creates dataset config


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates dataset config")
val dataset_config = {
    "path": "/data/mnist",
    "split": "train",
    "transform": true,
    "normalize": true
}
expect dataset_config["split"] == "train"
```

</details>

#### creates dataloader config

- creates dataloader config


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates dataloader config")
val loader_config = {
    "batch_size": 64,
    "shuffle": true,
    "num_workers": 4,
    "pin_memory": true
}
expect loader_config["batch_size"] == 64
expect loader_config["num_workers"] == 4
```

</details>

#### layer configurations

#### creates conv layer config

- creates conv layer config


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates conv layer config")
val conv_config = {
    "in_channels": 3,
    "out_channels": 64,
    "kernel_size": 3,
    "stride": 1,
    "padding": 1
}
expect conv_config["in_channels"] == 3
expect conv_config["out_channels"] == 64
```

</details>

#### creates linear layer config

- creates linear layer config


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates linear layer config")
val linear_config = {
    "in_features": 512,
    "out_features": 10,
    "bias": true
}
expect linear_config["bias"] == true
```

</details>

#### creates normalization config

- creates normalization config


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates normalization config")
val norm_config = {
    "num_features": 64,
    "eps": 1e-5,
    "momentum": 0.1,
    "affine": true
}
expect norm_config["num_features"] == 64
```

</details>

#### experiment tracking

#### creates experiment metadata

- creates experiment metadata


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates experiment metadata")
val experiment = {
    "name": "mnist_baseline",
    "version": "1.0.0",
    "author": "researcher",
    "timestamp": "2026-01-30"
}
expect experiment["name"] == "mnist_baseline"
```

</details>

#### stores metrics history

- stores metrics history


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores metrics history")
val metrics = {
    "train_loss": [0.5, 0.4, 0.3],
    "val_loss": [0.6, 0.5, 0.4],
    "train_acc": [0.85, 0.90, 0.93]
}
expect metrics["train_loss"].len() == 3
```

</details>

#### dict with torch types

#### stores device objects

- stores device objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores device objects")
val devices = {
    "gpu0": Device.CUDA(0),
    "gpu1": Device.CUDA(1),
    "cpu": Device.CPU
}
expect devices["cpu"] == Device.CPU
```

</details>

#### stores dtype configs

- stores dtype configs


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores dtype configs")
val dtypes = {
    "default": DType.Float32,
    "mixed": DType.Float16,
    "int": DType.Int64
}
expect dtypes["default"] == DType.Float32
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_async_mut/ml/dict_config_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering PyTorch Dict Configuration.
- PyTorch Dict Configuration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4509ffd00776772be0d80ed2063bb00f93dd3ccac3063be9ff77c0be43d470dd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4509ffd00776772be0d80ed2063bb00f93dd3ccac3063be9ff77c0be43d470dd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4509ffd00776772be0d80ed2063bb00f93dd3ccac3063be9ff77c0be43d470dd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/nogc_async_mut/ml/dict_config_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/ml/dict_config_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/ml/dict_config_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/ml/dict_config_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/ml/dict_config_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates model config dict' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/ml/dict_config_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates optimizer config' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/ml/dict_config_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates training config' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
