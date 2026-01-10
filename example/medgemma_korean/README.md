# MedGemma Korean - Progressive LoRA Training in Simple

Deep learning example demonstrating progressive LoRA training to prevent catastrophic forgetting, implemented in the Simple language.

## Overview

This example shows how to train a medical language model for Korean using **progressive LoRA stacking**, where each training phase adds a new LoRA adapter while freezing previous knowledge.

### Training Phases

```
Phase 0: Plain Text (Korean fluency)
    Base (frozen) + LoRA_0 (trainable)
    ↓
Phase 1: Medical Dictionary (terminology)
    [Base + LoRA_0] (frozen) + LoRA_1 (trainable)
    ↓
Phase 2: MCQ (medical reasoning)
    [Base + LoRA_0 + LoRA_1] (frozen) + LoRA_2 (trainable)
```

**Key Concept**: Each phase merges previous LoRAs into the base model, then adds a new trainable LoRA. This prevents catastrophic forgetting.

---

## Directory Structure

```
medgemma_korean/
├── README.md                    # This file
├── config/
│   ├── base.sdn                # Base configuration
│   ├── phase0.sdn              # Phase 0 config (plain text)
│   ├── phase1.sdn              # Phase 1 config (medical dict)
│   └── phase2.sdn              # Phase 2 config (MCQ)
├── src/
│   ├── lora_utils.spl          # LoRA merge/add utilities
│   ├── train_phase0.spl        # Phase 0: Plain text training
│   ├── train_phase1.spl        # Phase 1: Medical dict training
│   ├── train_phase2.spl        # Phase 2: MCQ training
│   └── validation.spl          # Validation utilities
├── data/
│   ├── plain_text/             # Korean text data
│   ├── medical_dict/           # Medical dictionary
│   └── mcq/                    # Multiple choice questions
└── models/
    ├── phase0/                 # Phase 0 outputs
    ├── phase1/                 # Phase 1 outputs
    └── phase2/                 # Phase 2 outputs (final)
```

---

## Features Demonstrated

### 1. Simple ML Infrastructure

- **Config System**: Hierarchical configuration with SDN format
- **Tracking System**: Experiment tracking (offline mode)
- **Engine System**: Event-driven training loops (PyTorch Ignite style)
- **Metrics**: Custom metrics (Loss, Accuracy, etc.)

### 2. Progressive LoRA Training

- **Merge previous LoRAs**: Freeze previous knowledge
- **Add new LoRA**: Only train new adapter
- **Prevent catastrophic forgetting**: Retain all previous phases

### 3. Korean Language Model Training

- **Phase 0**: Learn Korean language fluency
- **Phase 1**: Learn medical terminology
- **Phase 2**: Learn medical reasoning (MCQ)

---

## Quick Start

### Run All Phases

```bash
# Navigate to Simple root
cd simple

# Phase 0: Plain text training
./target/release/simple example/medgemma_korean/src/train_phase0.spl

# Phase 1: Medical dictionary training
./target/release/simple example/medgemma_korean/src/train_phase1.spl

# Phase 2: MCQ training
./target/release/simple example/medgemma_korean/src/train_phase2.spl
```

### Run Individual Phase

```bash
# With custom config
./target/release/simple example/medgemma_korean/src/train_phase1.spl \
    --config example/medgemma_korean/config/phase1.sdn \
    --epochs 5
```

---

## Configuration

Configurations use Simple Data Notation (SDN) format.

### Base Config (`config/base.sdn`)

```sdn
project: "medgemma-korean"
seed: 42

model:
  name: "google/medgemma-4b-it"
  lora_r: 64
  lora_alpha: 128
  lora_dropout: 0.05

training:
  batch_size: 4
  grad_accum: 4
  learning_rate: 0.0002
  max_length: 512
  device: "cuda:0"

tracking:
  mode: "offline"
  dir: ".simple/runs"
```

### Phase-specific configs extend base config.

---

## Training Process

### Phase 0: Plain Text

**Goal**: Learn Korean language fluency

```simple
import config
import ml.tracking as Track
import ml.engine.{Engine, Events, Loss}

# Load config
let cfg = config.from_file("config/phase0.sdn")

# Create run
let run = Track.run(
    project=cfg.get("project"),
    name="phase0-plain-text",
    config=cfg,
    tags=["phase0", "korean"]
)

# Define training step
fn train_step(engine: Engine, batch: any):
    # Forward pass
    output = model.forward(batch)
    loss = loss_fn(output)

    # Backward pass
    loss.backward()
    optimizer.step()

    return {"loss": loss.item()}

# Create engine
let trainer = Engine(train_step)

# Attach handlers
@trainer.on(Events.EPOCH_COMPLETED)
fn log_epoch(engine: Engine):
    run.log({
        "loss": engine.state.metrics["loss"],
        "epoch": engine.state.epoch
    }, step=engine.state.epoch)

# Run training
trainer.run(data_loader, max_epochs=cfg.get("training.epochs"))

# Save LoRA_0
save_lora(model, "models/phase0/lora_0")
run.finish()
```

### Phase 1: Medical Dictionary

**Goal**: Learn medical terminology (while preserving Korean fluency)

```simple
import lora_utils

# Load base model
model = load_base_model(cfg.get("model.name"))

# Merge LoRA_0 (freeze Phase 0 knowledge)
model = lora_utils.merge_lora(model, "models/phase0/lora_0")

# Add NEW LoRA_1 (trainable)
model = lora_utils.add_lora(model, cfg.get("model"))

# Train (only LoRA_1 updates)
trainer.run(dict_data_loader, max_epochs=cfg.get("training.epochs"))

# Save LoRA_1
save_lora(model, "models/phase1/lora_1")
```

### Phase 2: MCQ

**Goal**: Learn medical reasoning (while preserving Phase 0 + 1 knowledge)

```simple
# Merge LoRA_0 + LoRA_1 (freeze all previous knowledge)
model = load_base_model(cfg.get("model.name"))
model = lora_utils.merge_lora(model, "models/phase0/lora_0")
model = lora_utils.merge_lora(model, "models/phase1/lora_1")

# Add NEW LoRA_2 (trainable)
model = lora_utils.add_lora(model, cfg.get("model"))

# Train (only LoRA_2 updates)
trainer.run(mcq_data_loader, max_epochs=cfg.get("training.epochs"))

# Save LoRA_2
save_lora(model, "models/phase2/lora_2")
```

---

## Validation

After each phase, validate that previous knowledge is retained:

```simple
import validation

# After Phase 1, test both Phase 0 and Phase 1
validation.test_plain_text(model)  # Phase 0 knowledge
validation.test_medical_dict(model)  # Phase 1 knowledge

# After Phase 2, test all three
validation.test_plain_text(model)  # Phase 0 knowledge
validation.test_medical_dict(model)  # Phase 1 knowledge
validation.test_mcq(model)  # Phase 2 knowledge
```

---

## Event-Driven Training

Uses Simple's Engine (PyTorch Ignite style):

```simple
# Create engine
let trainer = Engine(train_step)

# Event: Log every 100 iterations
@trainer.on(Events.ITERATION_COMPLETED_EVERY(100))
fn log_iteration(engine: Engine):
    print(f"Step {engine.state.iteration}: loss={engine.state.output.loss}")

# Event: Validate every epoch
@trainer.on(Events.EPOCH_COMPLETED)
fn validate(engine: Engine):
    let val_loss = run_validation(model, val_loader)
    run.log({"val_loss": val_loss}, step=engine.state.epoch)

# Event: Save checkpoints
@trainer.on(Events.EPOCH_COMPLETED_EVERY(5))
fn save_checkpoint(engine: Engine):
    save_model(model, f"checkpoint_epoch_{engine.state.epoch}.pt")

# Event: Early stopping
@trainer.on(Events.EPOCH_COMPLETED)
fn early_stop(engine: Engine):
    if engine.state.metrics["loss"] < 0.01:
        engine.terminate()
```

---

## Metrics

Custom metrics track training progress:

```simple
import ml.engine.{Metric, Loss, Accuracy}

# Define custom metric
class MedicalAccuracy(Metric):
    correct: i64
    total: i64

    fn __init__(self):
        self.correct = 0
        self.total = 0

    fn reset(self):
        self.correct = 0
        self.total = 0

    fn update(self, output: any):
        # Check if predicted answer matches expected
        if output.predicted == output.expected:
            self.correct += 1
        self.total += 1

    fn compute(self) -> f64:
        return self.correct.to_f64() / self.total.to_f64()

# Add to engine
trainer.add_metric(MedicalAccuracy(), "med_acc")
```

---

## Experiment Tracking

All runs are tracked locally:

```
.simple/runs/
└── medgemma-korean/
    ├── run-phase0-001/
    │   ├── metadata.sdn        # Config, tags, timestamps
    │   ├── metrics.jsonl       # Training metrics
    │   └── artifacts/          # Saved models
    ├── run-phase1-001/
    └── run-phase2-001/
```

View run history:

```simple
import ml.tracking as Track

# List all runs
let runs = Track.list_runs(project="medgemma-korean")

for run in runs:
    print(f"Run {run.id}: {run.name} (accuracy: {run.summary.accuracy})")
```

---

## Advanced Features

### 1. Multi-GPU Training

```sdn
# config/multi_gpu.sdn
training:
  device: "cuda"  # Auto-distribute across all GPUs
  distributed: true
```

### 2. Custom Callbacks

```simple
class ProgressCallback(TrainerCallback):
    fn on_epoch_end(self, engine: Engine):
        print(f"Epoch {engine.state.epoch} complete!")
        print(f"Loss: {engine.state.metrics.loss:.4f}")

trainer.add_callback(ProgressCallback())
```

### 3. Hyperparameter Search

```simple
# Sweep over learning rates
for lr in [0.0001, 0.0002, 0.0005]:
    cfg.set("training.learning_rate", lr)

    let run = Track.run(
        project="medgemma-korean",
        name=f"lr_sweep_{lr}",
        config=cfg
    )

    train_and_evaluate(run, cfg)
    run.finish()
```

---

## Benefits of Simple Implementation

1. **Concise**: No boilerplate, clean syntax
2. **Type-safe**: Compile-time type checking
3. **Event-driven**: PyTorch Ignite style patterns
4. **Config management**: Built-in hierarchical configs
5. **Tracking**: Local-first experiment tracking
6. **No Python**: Pure Simple language (`.spl`)

---

## Comparison: Python vs Simple

### Python (before)
```python
# 50+ lines of imports
# Complex PEFT/transformers setup
# Manual event handling
# External config libraries (Hydra)
# External tracking (W&B)
```

### Simple (this example)
```simple
# 5 imports
import config
import ml.tracking as Track
import ml.engine.{Engine, Events}
import lora_utils

# Clean, integrated ML stack
# Built-in config/tracking/engine
```

---

## References

- **Simple Language Docs**: `simple/README.md`
- **ML Infrastructure Guide**: `simple/doc/guide/deeplearning.md`
- **Config System**: `simple/std_lib/src/config/`
- **Tracking System**: `simple/std_lib/src/ml/tracking/`
- **Engine System**: `simple/std_lib/src/ml/engine/`
- **Progressive LoRA Plan**: `medgemma_korean/PROGRESSIVE_LORA_PLAN.md`

---

## Next Steps

1. Run the example: `./target/release/simple example/medgemma_korean/src/train_phase0.spl`
2. Read the code: Explore `src/*.spl` files
3. Modify configs: Edit `config/*.sdn` files
4. Add custom metrics: Extend `validation.spl`
5. Experiment: Try different hyperparameters

This example demonstrates production-ready deep learning in Simple!
