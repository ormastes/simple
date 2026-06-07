# PyTorch Dictionary Configuration Specification

> Tests dictionary usage in PyTorch/ML contexts.

<!-- sdn-diagram:id=dict_config_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dict_config_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dict_config_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dict_config_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# PyTorch Dictionary Configuration Specification

Tests dictionary usage in PyTorch/ML contexts.

## At a Glance

| Field | Value |
|-------|-------|
| Category | ML, PyTorch |
| Status | Complete |
| Source | `test/01_unit/lib/ml/dict_config_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests dictionary usage in PyTorch/ML contexts.
Verifies that dict syntax works correctly for model configs,
hyperparameters, and training settings.
Local DType enum (runtime can't handle imported enum constructors)

## Scenarios

### PyTorch Dict Configuration

#### model configuration

#### creates model config dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt_config = {
    "lr": 0.001,
    "momentum": 0.9,
    "weight_decay": 0.0001
}
expect opt_config["lr"] == 0.001
```

</details>

#### creates training config

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val linear_config = {
    "in_features": 512,
    "out_features": 10,
    "bias": true
}
expect linear_config["bias"] == true
```

</details>

#### creates normalization config

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect metrics["train loss"] len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. "gpu0": Device CUDA
2. "gpu1": Device CUDA


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val devices = {
    "gpu0": Device.CUDA(0),
    "gpu1": Device.CUDA(1),
    "cpu": Device.CPU
}
expect devices["cpu"] == Device.CPU
```

</details>

#### stores dtype configs

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dtypes = {
    "default": DType.Float32,
    "mixed": DType.Float16,
    "int": DType.Int64
}
expect dtypes["default"] == DType.Float32
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
