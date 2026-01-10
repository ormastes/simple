# Deep Learning Skill - Simple Language

## When to Use This Skill

Use this skill when working with deep learning tasks in Simple:
- Training neural networks
- Progressive LoRA fine-tuning
- Experiment tracking and management
- Event-driven training loops
- Model validation and testing

## Core ML Infrastructure

### 1. Configuration System (`config`)

**Location**: `simple/std_lib/src/config/__init__.spl`

**Usage**:
```simple
import config

# Load from file
let cfg = config.from_file("config/base.sdn")

# Merge configs
let merged = config.merge(base_cfg, override_cfg)

# Access with dotted paths
let lr = cfg.get("training.learning_rate")
let epochs = cfg.get("training.epochs")

# Freeze config (immutable)
config.freeze(cfg)
```

**SDN Format**:
```sdn
# config/base.sdn
project: "my-project"
model:
  name: "google/gemma-2b"
  lora_r: 64
training:
  epochs: 3
  batch_size: 4
  learning_rate: 0.0002
```

---

### 2. Experiment Tracking (`ml.tracking`)

**Location**: `simple/std_lib/src/ml/tracking/__init__.spl`

**Usage**:
```simple
import ml.tracking as Track

# Set mode
Track.set_mode("offline")  # or "online", "disabled"

# Create run
let run = Track.run(
    project="cifar10",
    name="baseline",
    config=cfg,
    tags=["baseline", "resnet18"]
)

# Log metrics
run.log({"train/loss": 0.5, "train/acc": 0.92}, step=100)

# Log artifacts
let artifact = Track.Artifact("model-v1", type="model")
artifact.add_file("checkpoint.pt")
run.log_artifact(artifact, aliases=["latest", "best"])

# Finish
run.finish()
```

**Storage**:
- Local: `.simple/runs/{project}/{run_id}/`
- Metadata: `metadata.sdn`
- Metrics: `metrics.jsonl`
- Artifacts: `artifacts/`

---

### 3. Training Engine (`ml.engine`)

**Location**: `simple/std_lib/src/ml/engine/__init__.spl`

**Usage**:
```simple
import ml.engine.{Engine, Events, Loss, Accuracy}

# Define training step
fn train_step(engine: Engine, batch: any) -> {str: any}:
    # Forward pass
    let pred = model.forward(batch.x)
    let loss = loss_fn(pred, batch.y)

    # Backward pass
    loss.backward()
    optimizer.step()

    return {"loss": loss.item()}

# Create engine
let trainer = Engine(train_step)

# Add metrics
trainer.add_metrics({
    "loss": Loss(),
    "acc": Accuracy()
})

# Attach event handlers
@trainer.on(Events.STARTED)
fn on_start(engine: Engine):
    print("Training started!")

@trainer.on(Events.ITERATION_COMPLETED_EVERY(100))
fn log_iteration(engine: Engine):
    print(f"Step {engine.state.iteration}: loss={engine.state.output.loss}")

@trainer.on(Events.EPOCH_COMPLETED)
fn log_epoch(engine: Engine):
    print(f"Epoch {engine.state.epoch}: loss={engine.state.metrics.loss}")

# Run training
trainer.run(train_loader, max_epochs=10)
```

**Built-in Events**:
- `STARTED` - Engine started
- `EPOCH_STARTED` - Epoch started
- `ITERATION_STARTED` - Before batch
- `ITERATION_COMPLETED` - After batch
- `EPOCH_COMPLETED` - Epoch completed
- `COMPLETED` - All epochs done
- `EXCEPTION_RAISED` - Exception occurred

**Periodic Events**:
- `ITERATION_COMPLETED_EVERY(n)` - Every n iterations
- `EPOCH_COMPLETED_EVERY(n)` - Every n epochs

**Engine State**:
```simple
engine.state.epoch            # Current epoch
engine.state.iteration        # Global iteration count
engine.state.epoch_iteration  # Iteration within epoch
engine.state.max_epochs       # Total epochs
engine.state.output           # Last process function output
engine.state.metrics          # Computed metrics
engine.state.batch            # Current batch
```

---

### 4. Custom Metrics

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
        """Reset for new epoch."""
        self.tp = 0
        self.fp = 0
        self.fn = 0

    fn update(self, output: any):
        """Update with batch output."""
        # Compute tp, fp, fn from output
        pass

    fn compute(self) -> f64:
        """Compute final metric."""
        let precision = self.tp / (self.tp + self.fp)
        let recall = self.tp / (self.tp + self.fn)
        return 2.0 * precision * recall / (precision + recall)

# Use it
trainer.add_metric(F1Score(), "f1")
```

---

## Progressive LoRA Training

**Example**: `simple/example/medgemma_korean/`

### Pattern

```simple
import lora_utils.{LoRAConfig, progressive_lora_step}

# Phase 0: Base + LoRA_0
model = load_base_model("google/gemma-2b")
model = add_lora(model, lora_config)
train(model)
save_lora(model, "models/lora_0")

# Phase 1: Merge LoRA_0, add LoRA_1
model = load_base_model("google/gemma-2b")
model = progressive_lora_step(
    base_model=model,
    previous_loras=["models/lora_0"],
    new_lora_config=lora_config
)
train(model)
save_lora(model, "models/lora_1")

# Phase 2: Merge LoRA_0 + LoRA_1, add LoRA_2
model = progressive_lora_step(
    base_model=model,
    previous_loras=["models/lora_0", "models/lora_1"],
    new_lora_config=lora_config
)
train(model)
save_lora(model, "models/lora_2")
```

### Key Functions

**`merge_lora(model, lora_path)`**
- Merges LoRA weights into base model
- Freezes that knowledge
- Returns model with no LoRA (weights baked in)

**`add_lora(model, config)`**
- Adds new trainable LoRA adapter
- Base model weights frozen
- Returns model with trainable LoRA

**`progressive_lora_step(base_model, previous_loras, new_lora_config)`**
- One-step progressive LoRA pattern
- Merges all previous LoRAs
- Adds new trainable LoRA
- Returns model ready for training

---

## Complete Training Example

```simple
import config
import ml.tracking as Track
import ml.engine.{Engine, Events, Loss}
import lora_utils

# Load config
let cfg = config.from_file("config/train.sdn")

# Initialize tracking
Track.set_mode("offline")
let run = Track.run(
    project=cfg.get("project"),
    name="experiment-1",
    config=cfg,
    tags=["baseline"]
)

# Load model
let model = load_model(cfg.get("model.name"))
model = lora_utils.add_lora(model, lora_config)

# Define training step
fn train_step(engine: Engine, batch: any):
    optimizer.zero_grad()
    let output = model(batch.input_ids)
    let loss = loss_fn(output, batch.labels)
    loss.backward()
    optimizer.step()
    return {"loss": loss.item()}

# Create engine
let trainer = Engine(train_step)
trainer.add_metric(Loss(), "loss")

# Event handlers
@trainer.on(Events.ITERATION_COMPLETED_EVERY(100))
fn log_iteration(engine: Engine):
    run.log({"train/loss": engine.state.output.loss},
            step=engine.state.iteration)

@trainer.on(Events.EPOCH_COMPLETED)
fn log_epoch(engine: Engine):
    let loss = engine.state.metrics["loss"]
    print(f"Epoch {engine.state.epoch}: loss={loss:.4f}")
    run.log({"train/epoch_loss": loss}, step=engine.state.epoch)

@trainer.on(Events.COMPLETED)
fn on_complete(engine: Engine):
    lora_utils.save_lora(model, cfg.get("output.path"))

    let artifact = Track.Artifact("model-final", type="model")
    artifact.add_file(cfg.get("output.path"))
    run.log_artifact(artifact, aliases=["latest"])

# Train
trainer.run(train_loader, max_epochs=cfg.get("training.epochs"))
run.finish()
```

---

## Validation and Testing

**Example**: `simple/example/medgemma_korean/src/validation.spl`

```simple
import validation.{test_all_phases, ValidationReport}

# After each training phase
let report = test_all_phases(
    model=model,
    tokenizer=tokenizer,
    mcq_test_data=test_data,
    device="cuda:0"
)

report.print()

# Check for catastrophic forgetting
if report.has_catastrophic_forgetting():
    print("ERROR: Catastrophic forgetting detected!")
    # Take corrective action
```

**Quick retention check during training**:
```simple
import validation.validate_no_forgetting

@trainer.on(Events.EPOCH_COMPLETED)
fn check_retention(engine: Engine):
    if not validate_no_forgetting(
        current_phase=2,
        model=model,
        tokenizer=tokenizer,
        device="cuda:0"
    ):
        print("WARNING: Previous knowledge lost!")
        engine.terminate()
```

---

## File Organization

### Recommended Structure

```
project/
├── config/
│   ├── base.sdn              # Base config
│   ├── train.sdn             # Training config
│   └── eval.sdn              # Evaluation config
├── src/
│   ├── train.spl             # Training script
│   ├── evaluate.spl          # Evaluation script
│   ├── models.spl            # Model definitions
│   └── utils.spl             # Utilities
├── data/
│   ├── train/
│   └── val/
└── models/
    ├── checkpoints/
    └── final/
```

---

## Best Practices

### 1. Configuration Management

✅ **DO**:
- Use SDN files for all configs
- Use `config.merge()` for overrides
- Freeze configs before training
- Store hyperparameters in config

❌ **DON'T**:
- Hardcode hyperparameters
- Modify configs during training
- Use global variables

### 2. Experiment Tracking

✅ **DO**:
- Use offline mode for local experiments
- Log at consistent intervals
- Save artifacts with meaningful names
- Tag runs for organization

❌ **DON'T**:
- Log every iteration (too much data)
- Forget to call `run.finish()`
- Overwrite previous experiments

### 3. Training Loops

✅ **DO**:
- Use Engine for training loops
- Keep `train_step` pure (no side effects)
- Use event handlers for logging
- Implement early stopping when needed

❌ **DON'T**:
- Write manual training loops
- Put complex logic in `train_step`
- Ignore engine state

### 4. Progressive LoRA

✅ **DO**:
- Merge previous LoRAs before adding new one
- Validate knowledge retention after each phase
- Save each LoRA separately
- Test that previous knowledge is retained

❌ **DON'T**:
- Reuse same LoRA across phases
- Skip validation tests
- Assume knowledge is retained

---

## Common Patterns

### Pattern 1: Multi-Phase Training

```simple
# Phase 1
let model = train_phase(data1, lora_config)
save_lora(model, "lora_1")

# Phase 2
model = progressive_lora_step(
    base_model,
    ["lora_1"],
    lora_config
)
model = train_phase(data2, lora_config)
save_lora(model, "lora_2")
```

### Pattern 2: Checkpointing

```simple
@trainer.on(Events.EPOCH_COMPLETED_EVERY(5))
fn save_checkpoint(engine: Engine):
    let path = f"checkpoints/epoch_{engine.state.epoch}.pt"
    save_model(model, path)
```

### Pattern 3: Early Stopping

```simple
@trainer.on(Events.EPOCH_COMPLETED)
fn early_stop(engine: Engine):
    if engine.state.metrics["loss"] < 0.01:
        print("Target reached!")
        engine.terminate()
```

### Pattern 4: Learning Rate Scheduling

```simple
@trainer.on(Events.EPOCH_COMPLETED)
fn update_lr(engine: Engine):
    if engine.state.epoch > 5:
        optimizer.lr *= 0.9
```

---

## References

- **Deep Learning Guide**: `simple/doc/guide/deeplearning.md`
- **Example Project**: `simple/example/medgemma_korean/`
- **Config System**: `simple/std_lib/src/config/`
- **Tracking System**: `simple/std_lib/src/ml/tracking/`
- **Engine System**: `simple/std_lib/src/ml/engine/`
- **BDD Specs**: `simple/std_lib/test/features/ml/`

---

## Troubleshooting

### Issue: Config not loading
```simple
# Check file exists
import fs
if not fs.exists("config/base.sdn"):
    print("Config file not found!")

# Check syntax
# SDN uses: key: value (not key = value)
```

### Issue: Metrics not updating
```simple
# Ensure metric.update() is called
fn train_step(engine, batch):
    result = ...
    return result  # This gets passed to metric.update()

# Ensure metric is added to engine
trainer.add_metric(MyMetric(), "my_metric")
```

### Issue: Events not firing
```simple
# Check event name spelling
@trainer.on(Events.EPOCH_COMPLETED)  # Correct
# @trainer.on("epoch_completed")     # Wrong

# Check engine.run() is called
trainer.run(data, max_epochs=10)
```

### Issue: Progressive LoRA forgetting
```simple
# Verify merge_lora is called
model = merge_lora(model, "lora_0")  # Freezes LoRA_0

# Verify is_trainable=False when loading
model = load_lora(model, "lora_0", trainable=false)

# Add validation checks
validate_no_forgetting(phase, model, tokenizer, device)
```

---

## See Also

- `/coding` - Simple language coding standards
- `/test` - Writing tests in Simple
- `/design` - API design patterns
- `/stdlib` - Standard library modules
