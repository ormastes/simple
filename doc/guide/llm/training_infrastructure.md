# Deep Learning with Simple

Complete guide to building and training deep learning models using Simple's ML infrastructure.

## Table of Contents

1. [Overview](#overview)
2. [ML Infrastructure](#ml-infrastructure)
3. [Configuration System](#configuration-system)
4. [Experiment Tracking](#experiment-tracking)
5. [Training Engine](#training-engine)
6. [Complete Workflow](#complete-workflow)
7. [PyTorch Ignite-style Training](#pytorch-ignite-style-training)
8. [Best Practices](#best-practices)

---

## Overview

Simple provides a batteries-included ML infrastructure inspired by modern Python frameworks:

- **Configuration**: Hierarchical config with SDN format (like Hydra)
- **Tracking**: Local-first experiment tracking (like W&B)
- **Engine**: Event-driven training loops (like PyTorch Ignite)
- **Metrics**: Reusable metric classes (Loss, Accuracy, etc.)
- **Caching**: Memory-aware data caching
- **Validation**: Runtime validation for models/data

All components work together seamlessly and use `.spl` format (no Python required).

---

## ML Infrastructure

### Module Structure

```
simple/std_lib/src/
├── config/              # Configuration system
│   └── __init__.spl
├── ml/
│   ├── tracking/        # Experiment tracking
│   │   └── __init__.spl
│   ├── engine/          # Training engine
│   │   └── __init__.spl
│   ├── torch/           # PyTorch FFI
│   │   ├── nn/          # Neural network layers
│   │   ├── optim/       # Optimizers
│   │   ├── autograd/    # Automatic differentiation
│   │   ├── data.spl     # DataLoader
│   │   └── utils.spl    # Utilities
│   └── ...
└── ...
```

### Key Components

| Component | Purpose | Inspiration |
|-----------|---------|-------------|
| `config` | Hierarchical configuration | Hydra, OmegaConf |
| `ml.tracking` | Experiment logging | W&B, MLflow |
| `ml.engine` | Event-driven training | PyTorch Ignite |
| `ml.torch.*` | Deep learning primitives | PyTorch |

---

## Configuration System

### Basic Usage

```simple
import config

# Create configuration from dict
let base_config = {
    "project": "cifar10",
    "seed": 42,
    "train": {
        "epochs": 10,
        "batch_size": 64,
        "lr": 0.001
    },
    "model": {
        "type": "resnet18",
        "hidden_size": 128
    }
}

let cfg = config.from_dict(base_config)

# Access with dotted paths
print(cfg.get("train.epochs"))       # 10
print(cfg.get("train.lr"))           # 0.001
print(cfg.get("model.hidden_size"))  # 128
```

### Merging Configurations

```simple
# Base config
let base = config.from_dict({
    "epochs": 10,
    "lr": 0.001,
    "batch_size": 64
})

# Override config
let override = config.from_dict({
    "epochs": 20,
    "lr": 0.005
})

# Merge (override takes precedence)
let merged = config.merge(base, override)

print(merged.get("epochs"))      # 20 (overridden)
print(merged.get("lr"))          # 0.005 (overridden)
print(merged.get("batch_size"))  # 64 (from base)
```

### CLI Integration

```simple
# Parse CLI arguments like "--train.epochs=20"
let cli_args = ["train.epochs=20", "train.lr=0.005"]
let cli_cfg = config.from_cli_dotlist(cli_args)

# Merge with base config
let final_cfg = config.merge(base_cfg, cli_cfg)
```

### Freezing Config

```simple
# Freeze config to prevent modifications
config.freeze(cfg)

# Now cfg is immutable
```

---

## Experiment Tracking

### Run Lifecycle

```simple
import ml.tracking as Track

# Set mode: "online", "offline", "disabled"
Track.set_mode("offline")

# Create a run
let run = Track.run(
    project="cifar10",
    name="baseline-experiment",
    config={"lr": 0.001, "batch_size": 64},
    tags=["baseline", "resnet18"]
)

# Log metrics
for epoch in 0..num_epochs:
    run.log({
        "train/loss": train_loss,
        "train/acc": train_acc,
        "epoch": epoch
    }, step=epoch)

# Save model artifact
let artifact = Track.Artifact(
    name="model-v1",
    type="model",
    description="Baseline ResNet18"
)
artifact.add_file("checkpoint.pt")
run.log_artifact(artifact, aliases=["latest", "best"])

# Finish run
run.finish()
```

### Directory Structure

Runs are stored locally in `.simple/runs/`:

```
.simple/runs/
└── cifar10/               # Project name
    └── run-001/           # Run ID
        ├── metadata.sdn   # Run metadata (config, tags, etc.)
        ├── metrics.jsonl  # Metrics (one JSON per line)
        ├── media/         # Images, plots
        │   └── images/
        └── artifacts/     # Model checkpoints, results
            └── model-v1/
                ├── metadata.sdn
                └── checkpoint.pt
```

### Logging Different Data Types

```simple
# Scalars
run.log({"loss": 0.5, "acc": 0.92}, step=100)

# Histograms
run.log_histogram(
    name="weights",
    values=layer_weights,
    bins=50,
    step=100
)

# Images
run.log_image(
    name="prediction",
    image_path="pred.png",
    caption="Model prediction",
    step=100
)
```

---

## Training Engine

### Basic Training Loop

```simple
import ml.engine.{Engine, Events, Loss}

# Define training step
fn train_step(engine: Engine, batch: any) -> {str: any}:
    model.train()
    let (x, y) = batch

    # Forward pass
    let pred = model.forward(x)
    let loss = loss_fn(pred, y)

    # Backward pass
    loss.backward()
    optimizer.step()
    optimizer.zero_grad()

    return {"loss": loss.item()}

# Create trainer
let trainer = Engine(train_step)

# Run training
trainer.run(train_loader, max_epochs=10)
```

### Event Handlers

```simple
# Attach handlers to events
@trainer.on(Events.STARTED)
fn on_start(engine: Engine):
    print("Training started!")

@trainer.on(Events.EPOCH_STARTED)
fn on_epoch_start(engine: Engine):
    print(f"Epoch {engine.state.epoch + 1}/{engine.state.max_epochs}")

@trainer.on(Events.ITERATION_COMPLETED)
fn log_iteration(engine: Engine):
    if engine.state.iteration % 100 == 0:
        print(f"Step {engine.state.iteration}: loss={engine.state.output['loss']:.4f}")

@trainer.on(Events.EPOCH_COMPLETED)
fn on_epoch_complete(engine: Engine):
    print(f"Epoch {engine.state.epoch + 1} completed")
    print(f"Avg loss: {engine.state.metrics['loss']:.4f}")

@trainer.on(Events.COMPLETED)
fn on_complete(engine: Engine):
    print("Training finished!")
```

### Periodic Events

```simple
# Run every 100 iterations
@trainer.on(Events.ITERATION_COMPLETED_EVERY(100))
fn log_every_100(engine: Engine):
    print(f"Step {engine.state.iteration}")

# Run every 5 epochs
@trainer.on(Events.EPOCH_COMPLETED_EVERY(5))
fn validate_every_5(engine: Engine):
    evaluate(model, val_loader)
```

### Built-in Events

| Event | When Fired |
|-------|-----------|
| `STARTED` | Engine starts |
| `EPOCH_STARTED` | Epoch starts |
| `ITERATION_STARTED` | Before batch processing |
| `ITERATION_COMPLETED` | After batch processing |
| `EPOCH_COMPLETED` | Epoch completes |
| `COMPLETED` | Engine completes all epochs |
| `EXCEPTION_RAISED` | Exception during execution |

### Metrics

```simple
import ml.engine.{Loss, Accuracy}

# Add metrics to engine
let loss_metric = Loss()
let acc_metric = Accuracy()

trainer.add_metrics({
    "loss": loss_metric,
    "acc": acc_metric
})

# Metrics are computed automatically and stored in engine.state.metrics
@trainer.on(Events.EPOCH_COMPLETED)
fn log_metrics(engine: Engine):
    print(f"Loss: {engine.state.metrics['loss']:.4f}")
    print(f"Acc: {engine.state.metrics['acc']:.4f}")
```

### Custom Metrics

```simple
import ml.engine.Metric

class F1Score(Metric):
    tp: i64
    fp: i64
    fn: i64

    fn __init__(self):
        self.tp = 0
        self.fp = 0
        self.fn = 0

    fn reset(self):
        self.tp = 0
        self.fp = 0
        self.fn = 0

    fn update(self, output: any):
        let (pred, target) = output
        # Compute tp, fp, fn
        # ...

    fn compute(self) -> f64:
        let precision = self.tp / (self.tp + self.fp)
        let recall = self.tp / (self.tp + self.fn)
        return 2.0 * precision * recall / (precision + recall)

# Use custom metric
let f1 = F1Score()
trainer.add_metric(f1, "f1")
```

### Engine State

Access current state via `engine.state`:

```simple
engine.state.epoch            # Current epoch (0-indexed)
engine.state.iteration        # Global iteration counter
engine.state.epoch_iteration  # Iteration within current epoch
engine.state.max_epochs       # Total epochs
engine.state.output           # Return value of process function
engine.state.metrics          # Computed metrics dict
engine.state.batch            # Current batch
```

### Early Stopping

```simple
@trainer.on(Events.EPOCH_COMPLETED)
fn early_stopping(engine: Engine):
    if engine.state.metrics["loss"] < 0.01:
        print("Loss target reached, stopping early")
        engine.terminate()
```

---

## Complete Workflow

### Full Training Example

```simple
import config
import ml.tracking as Track
import ml.engine.{Engine, Events, Loss, Accuracy}
import ml.torch.{nn, optim, data}

# ============================================================================
# 1. Configuration
# ============================================================================

let base_config = {
    "project": "mnist-classifier",
    "seed": 42,
    "train": {
        "epochs": 10,
        "batch_size": 64,
        "lr": 0.001,
        "device": "cuda"
    },
    "model": {
        "hidden_size": 128,
        "dropout": 0.2
    }
}

let cfg = config.from_dict(base_config)

# ============================================================================
# 2. Data Loading
# ============================================================================

let train_dataset = data.MNIST(root="./data", train=true, download=true)
let val_dataset = data.MNIST(root="./data", train=false)

let train_loader = data.DataLoader(
    train_dataset,
    batch_size=cfg.get("train.batch_size"),
    shuffle=true
)

let val_loader = data.DataLoader(
    val_dataset,
    batch_size=cfg.get("train.batch_size"),
    shuffle=false
)

# ============================================================================
# 3. Model Definition
# ============================================================================

class MNISTClassifier(nn.Module):
    fc1: nn.Linear
    fc2: nn.Linear
    dropout: nn.Dropout

    fn __init__(self):
        super().__init__()
        self.fc1 = nn.Linear(784, cfg.get("model.hidden_size"))
        self.fc2 = nn.Linear(cfg.get("model.hidden_size"), 10)
        self.dropout = nn.Dropout(cfg.get("model.dropout"))

    fn forward(self, x: Tensor) -> Tensor:
        x = x.view(-1, 784)
        x = self.fc1(x).relu()
        x = self.dropout(x)
        x = self.fc2(x)
        return x

let model = MNISTClassifier()
model.to(cfg.get("train.device"))

# ============================================================================
# 4. Optimizer & Loss
# ============================================================================

let optimizer = optim.Adam(model.parameters(), lr=cfg.get("train.lr"))
let loss_fn = nn.CrossEntropyLoss()

# ============================================================================
# 5. Experiment Tracking
# ============================================================================

Track.set_mode("offline")
let run = Track.run(
    project=cfg.get("project"),
    name="baseline",
    config=config.to_dict(cfg),
    tags=["baseline", "mnist"]
)

# ============================================================================
# 6. Training Engine
# ============================================================================

fn train_step(engine: Engine, batch: any) -> {str: any}:
    model.train()
    optimizer.zero_grad()

    let (x, y) = batch
    x = x.to(cfg.get("train.device"))
    y = y.to(cfg.get("train.device"))

    let pred = model.forward(x)
    let loss = loss_fn(pred, y)

    loss.backward()
    optimizer.step()

    return {
        "loss": loss.item(),
        "pred": pred.argmax(dim=1),
        "labels": y
    }

let trainer = Engine(train_step)

# Add metrics
trainer.add_metrics({
    "loss": Loss(),
    "acc": Accuracy()
})

# ============================================================================
# 7. Event Handlers
# ============================================================================

@trainer.on(Events.STARTED)
fn on_start(engine: Engine):
    print("Training started!")

@trainer.on(Events.ITERATION_COMPLETED_EVERY(100))
fn log_iteration(engine: Engine):
    run.log({
        "train/loss": engine.state.output["loss"],
        "step": engine.state.iteration
    }, step=engine.state.iteration)

@trainer.on(Events.EPOCH_COMPLETED)
fn log_epoch(engine: Engine):
    let epoch = engine.state.epoch + 1
    let loss = engine.state.metrics["loss"]
    let acc = engine.state.metrics["acc"]

    print(f"Epoch {epoch}/{engine.state.max_epochs}")
    print(f"  Train - Loss: {loss:.4f}, Acc: {acc:.4f}")

    run.log({
        "train/epoch_loss": loss,
        "train/epoch_acc": acc,
        "epoch": epoch
    }, step=epoch)

    # Validation
    let val_loss, val_acc = evaluate(model, val_loader, loss_fn)
    print(f"  Val   - Loss: {val_loss:.4f}, Acc: {val_acc:.4f}")

    run.log({
        "val/loss": val_loss,
        "val/acc": val_acc,
        "epoch": epoch
    }, step=epoch)

    # Save checkpoint
    torch.save(model.state_dict(), f"checkpoint_epoch_{epoch}.pt")

@trainer.on(Events.COMPLETED)
fn on_complete(engine: Engine):
    print("Training completed!")

    # Save final model
    let artifact = Track.Artifact(
        name="mnist-model-final",
        type="model",
        description="Final MNIST classifier"
    )
    artifact.add_file(f"checkpoint_epoch_{engine.state.max_epochs}.pt")
    run.log_artifact(artifact, aliases=["latest", "final"])

# ============================================================================
# 8. Validation Function
# ============================================================================

fn evaluate(model: nn.Module, loader: data.DataLoader, loss_fn: any) -> (f64, f64):
    model.eval()
    let mut total_loss = 0.0
    let mut correct = 0
    let mut total = 0

    for batch in loader:
        let (x, y) = batch
        x = x.to(cfg.get("train.device"))
        y = y.to(cfg.get("train.device"))

        let pred = model.forward(x)
        let loss = loss_fn(pred, y)

        total_loss += loss.item()
        correct += (pred.argmax(dim=1) == y).sum().item()
        total += y.size(0)

    let avg_loss = total_loss / loader.len()
    let accuracy = correct / total

    return (avg_loss, accuracy)

# ============================================================================
# 9. Run Training
# ============================================================================

trainer.run(train_loader, max_epochs=cfg.get("train.epochs"))

run.finish()
print(f"\nExperiment saved to: {run.dir}")
```

---

## PyTorch Ignite-style Training

Simple's Engine is inspired by PyTorch Ignite and supports similar patterns.

### Comparison

| PyTorch Ignite | Simple Engine |
|----------------|---------------|
| `Engine(process_function)` | `Engine(process_function)` |
| `@trainer.on(Events.STARTED)` | `@trainer.on(Events.STARTED)` |
| `engine.state.epoch` | `engine.state.epoch` |
| `engine.run(data, max_epochs)` | `engine.run(data, max_epochs)` |

### Handler Priorities

```simple
# Higher priority = runs earlier
trainer.attach_handler(Events.EPOCH_COMPLETED, early_handler, priority=10)
trainer.attach_handler(Events.EPOCH_COMPLETED, late_handler, priority=0)
```

### Multiple Engines

```simple
# Training engine
let trainer = Engine(train_step)

# Evaluation engine
let evaluator = Engine(eval_step)

# Run evaluator every epoch
@trainer.on(Events.EPOCH_COMPLETED)
fn validate(engine: Engine):
    evaluator.run(val_loader, max_epochs=1)
    print(f"Val loss: {evaluator.state.metrics['loss']:.4f}")
```

---

## Best Practices

### 1. Configuration

✅ **DO**:
- Use hierarchical configs with nested dicts
- Freeze configs before training
- Merge CLI args with base config
- Store all hyperparameters in config

❌ **DON'T**:
- Hardcode hyperparameters
- Modify config during training
- Use global variables for settings

### 2. Experiment Tracking

✅ **DO**:
- Use offline mode for local experiments
- Log metrics at consistent intervals
- Save model artifacts with meaningful names
- Tag runs for easy filtering
- Log both training and validation metrics

❌ **DON'T**:
- Log every iteration (too much data)
- Forget to call `run.finish()`
- Overwrite previous experiments

### 3. Training Engine

✅ **DO**:
- Keep `process_function` pure (no side effects)
- Use event handlers for logging/validation
- Implement early stopping when needed
- Reset model state between epochs

❌ **DON'T**:
- Put complex logic in `process_function`
- Forget to call `model.train()` / `model.eval()`
- Ignore engine state

### 4. Code Organization

```
project/
├── configs/              # Configuration files
│   ├── base.sdn
│   ├── resnet18.sdn
│   └── mobilenet.sdn
├── data/                 # Datasets
├── models/               # Model definitions
│   ├── resnet.spl
│   └── mobilenet.spl
├── train.spl             # Training script
├── evaluate.spl          # Evaluation script
└── utils/                # Helper functions
    ├── metrics.spl
    └── transforms.spl
```

### 5. Logging Strategy

```simple
# Log at different frequencies
@trainer.on(Events.ITERATION_COMPLETED_EVERY(100))
fn log_iteration_metrics(engine: Engine):
    # Frequent: loss per 100 iterations
    run.log({"train/loss": engine.state.output["loss"]}, step=engine.state.iteration)

@trainer.on(Events.EPOCH_COMPLETED)
fn log_epoch_metrics(engine: Engine):
    # Less frequent: aggregated metrics per epoch
    run.log({
        "train/epoch_loss": engine.state.metrics["loss"],
        "train/epoch_acc": engine.state.metrics["acc"]
    }, step=engine.state.epoch)
```

### 6. Checkpoint Strategy

```simple
@trainer.on(Events.EPOCH_COMPLETED)
fn save_checkpoint(engine: Engine):
    let epoch = engine.state.epoch + 1

    # Save every epoch
    torch.save(model.state_dict(), f"checkpoint_epoch_{epoch}.pt")

    # Save best model
    if engine.state.metrics["loss"] < best_loss:
        torch.save(model.state_dict(), "best_model.pt")
        best_loss = engine.state.metrics["loss"]
```

---

## Examples

See these files for working examples:

- **Config**: `simple/std_lib/example/ml/config_example.spl`
- **Tracking**: `simple/std_lib/example/ml/tracking_example.spl`
- **Engine**: `simple/std_lib/example/ml/engine_example.spl`
- **Complete**: `simple/std_lib/example/ml/train_example.spl`

---

## References

### Simple Modules

- `simple/std_lib/src/config/__init__.spl` - Configuration system
- `simple/std_lib/src/ml/tracking/__init__.spl` - Experiment tracking
- `simple/std_lib/src/ml/engine/__init__.spl` - Training engine
- `simple/std_lib/src/ml/torch/` - PyTorch FFI bindings

### External Inspiration

- **PyTorch Ignite**: Event-driven training loops
- **Weights & Biases**: Experiment tracking
- **Hydra**: Configuration management
- **PyTorch**: Deep learning framework

---

## Next Steps

1. Run the examples in `simple/std_lib/example/ml/`
2. Read the BDD specs in `simple/std_lib/test/features/ml/`
3. Check integration tests in `simple/std_lib/test/integration/ml/`
4. Build your own training pipeline using the complete workflow above

For questions, see `CLAUDE.md` or invoke skills with `/deeplearning`.
