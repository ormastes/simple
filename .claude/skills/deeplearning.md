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

**Location**: `src/std/src/config/__init__.spl`

**Usage**:
```simple
import config

# Load from file
cfg = config.from_file("config/base.sdn")

# Merge configs
merged = config.merge(base_cfg, override_cfg)

# Access with dotted paths
lr = cfg.get("training.learning_rate")
epochs = cfg.get("training.epochs")

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

**Location**: `src/std/src/ml/tracking/__init__.spl`

**Usage**:
```simple
import ml.tracking as Track

# Set mode
Track.set_mode("offline")  # or "online", "disabled"

# Create run
run = Track.run(
    project="cifar10",
    name="baseline",
    config=cfg,
    tags=["baseline", "resnet18"]
)

# Log metrics
run.log({"train/loss": 0.5, "train/acc": 0.92}, step=100)

# Log artifacts
artifact = Track.Artifact("model-v1", type="model")
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

**Location**: `src/std/src/ml/engine/__init__.spl`

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
    fn_count: i64

    static fn new() -> F1Score:
        F1Score(tp: 0, fp: 0, fn_count: 0)

    me reset():
        """Reset for new epoch."""
        self.tp = 0
        self.fp = 0
        self.fn_count = 0

    me update(output: any):
        """Update with batch output."""
        # Compute tp, fp, fn from output
        pass

    fn compute() -> f64:
        """Compute final metric."""
        precision = self.tp / (self.tp + self.fp)
        recall = self.tp / (self.tp + self.fn_count)
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
- **Config System**: `src/std/src/config/`
- **Tracking System**: `src/std/src/ml/tracking/`
- **Engine System**: `src/std/src/ml/engine/`
- **BDD Specs**: `src/std/test/features/ml/`

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

---

## Pipeline Operators and Dimension Checking

Simple provides pipeline operators for functional composition and neural network layer chaining, with **compile-time dimension checking** to catch shape mismatches early.

### Pipeline Operators

| Operator | Name | Description |
|----------|------|-------------|
| `\|>` | Pipe Forward | Pass value to function: `x \|> f` = `f(x)` |
| `>>` | Compose | Forward composition: `f >> g` = `λx. g(f(x))` |
| `<<` | Compose Back | Backward composition: `f << g` = `λx. f(g(x))` |
| `//` | Parallel | Parallel branches: `f // g` runs both |
| `~>` | Layer Connect | NN layer pipeline with dimension checking |

### Precedence (Low to High)

```
15. Pipeline (|>, ~>)     ← Lowest
14. Parallel (//)
13. Compose (>>, <<)
12. Logical OR (or, ||)
11. Logical AND (and, &&)
... (standard operators)
1.  Primary               ← Highest
```

---

### Pipe Forward (`|>`)

Pass the left operand as the first argument to the right operand.

```simple
# Basic usage
val result = 5 |> double |> square |> to_string
# Equivalent to: to_string(square(double(5)))

# Data processing pipeline
val output = raw_input
    |> parse_json
    |> validate
    |> transform
    |> serialize

# With lambdas
val processed = data
    |> \x: x.filter(\item: item > 0)
    |> \x: x.map(\item: item * 2)
    |> \x: x.sum()
```

---

### Function Composition (`>>`, `<<`)

Create reusable pipelines by composing functions.

```simple
# Create reusable pipeline
val preprocess = normalize >> augment >> to_tensor
val result = preprocess(raw_data)

# Backward composition (Haskell-style)
val pipeline = serialize << transform << validate
# Same as: validate >> transform >> serialize

# Point-free style
val double = \x: x * 2
val square = \x: x * x
val double_then_square = double >> square

assert double_then_square(3) == 36  # (3 * 2)^2
```

---

### Layer Connect (`~>`) - **Dimension Checked**

Compose neural network layers with **compile-time dimension checking**.

```simple
# MLP with dimension checking
val mlp = Linear(784, 256) ~> ReLU() ~> Linear(256, 128) ~> ReLU() ~> Linear(128, 10)
# Type: Layer<[batch, 784], [batch, 10]>

# CNN encoder
val encoder = Conv2d(1, 32, 3) ~> ReLU() ~> MaxPool2d(2)
              ~> Conv2d(32, 64, 3) ~> ReLU() ~> MaxPool2d(2)
              ~> Flatten() ~> Linear(1600, 256)

# Autoencoder
val encoder = Linear(784, 256) ~> ReLU() ~> Linear(256, 64)
val decoder = Linear(64, 256) ~> ReLU() ~> Linear(256, 784)
val autoencoder = encoder ~> decoder
# Type: Layer<[batch, 784], [batch, 784]>
```

**Compile-Time Error Example:**
```simple
# ERROR: dimension mismatch
val bad = Linear(784, 256) ~> Linear(128, 64)
```

```
error[E0502]: layer dimension mismatch in ~> pipeline
  --> model.spl:1:35
   |
   = found: previous layer outputs shape: [batch, 256]
   = expected: next layer expects input shape: [batch, 128]
   = note: dimension 1 differs: 256 vs 128
   = help: insert Linear(256, 128) between these layers
```

---

### Parallel Branches (`//`)

Run two operations in parallel, combining their results.

```simple
# Parallel function application
val both = inc // dec
val (a, b) = both(5, 5)  # (6, 4)

# Parallel data processing
val process_both = encode_audio // encode_video
val (audio, video) = process_both(raw_audio, raw_video)

# Neural network parallel branches
val features = conv_branch // pool_branch
```

---

## Tensor and Matrix Operators

### Matrix Operations

```simple
val A: Tensor<f32, [M, K]> = ...
val B: Tensor<f32, [K, N]> = ...

# Matrix multiplication (dimension checked)
val C = A @ B    # Result: Tensor<f32, [M, N]>

# Transpose
val At = A.T     # Tensor<f32, [K, M]>

# Element-wise with broadcasting
val D = A .+ 1.0  # Add scalar to all elements
val E = A .* B    # Element-wise multiply (must broadcast)
```

### Dotted Operators (Element-wise Broadcasting)

| Operator | Description |
|----------|-------------|
| `.+` | Broadcast add |
| `.-` | Broadcast subtract |
| `.*` | Broadcast multiply |
| `./` | Broadcast divide |
| `.^` | Broadcast power |

```simple
# Broadcasting example
val a: Tensor<f32, [32, 1]> = ...
val b: Tensor<f32, [1, 64]> = ...
val c = a .+ b   # Result: Tensor<f32, [32, 64]>
```

---

## Dimension Types

### DimExpr (Dimension Expression)

```simple
# Literal dimension
784

# Named dimension with range
batch: 1..128

# Dynamic (runtime only)
?

# Const parameter
N  # from generic: fn process<N>(...)

# Arithmetic
M * K
H / num_heads
```

### Tensor Type Syntax

```simple
# Fixed dimensions
Tensor<f32, [32, 784]>

# Named/symbolic dimensions
Tensor<f32, [batch, seq_len, hidden]>

# With constraints
Tensor<f32, [B: 1..128, T: 1..512, D]>
```

### Layer Type Syntax

```simple
# Input → Output shape
Layer<[batch, 784], [batch, 256]>

# With explicit annotation
val encoder: Layer<[batch, 784], [batch, 64]> =
    Linear(784, 256) ~> ReLU() ~> Linear(256, 64)
```

---

## Dimension Error Codes

| Code | Name | Description | Quick Fix |
|------|------|-------------|-----------|
| E0501 | Mismatch | Basic dimension mismatch | Reshape/match dims |
| E0502 | LayerIncompatible | Layer output/input mismatch | Add intermediate layer |
| E0503 | RankMismatch | Tensor rank (ndim) mismatch | Flatten/reshape |
| E0504 | MatMulIncompat | Matrix multiplication K mismatch | Transpose or reshape |
| E0505 | BroadcastIncompat | Cannot broadcast shapes | Add dims with unsqueeze |
| E0506 | BatchMismatch | Batch dimension mismatch | Use same batch size |
| E0507 | ChannelMismatch | CNN channel mismatch | Fix Conv2d params |
| E0508 | SequenceMismatch | Sequence length mismatch | Pad/truncate |
| E0509 | OutOfRange | Value out of range | Use valid value |
| E0510 | UnresolvedVariable | Can't infer dimension | Add annotation |

### Common Error Fixes

**E0502: Layer Incompatible**
```simple
# Error
val model = Linear(784, 256) ~> Linear(128, 64)
# output [batch, 256] != input [batch, 128]

# Fix: Add intermediate layer
val model = Linear(784, 256) ~> Linear(256, 128) ~> Linear(128, 64)
```

**E0503: Rank Mismatch**
```simple
# Error: 4D tensor to 2D layer
val conv_out: Tensor<f32, [batch, 64, 7, 7]> = ...
val fc = Linear(64, 10)
val out = conv_out ~> fc  # E0503: 4D vs 2D

# Fix: Flatten before Linear
val model = Flatten() ~> Linear(3136, 10)  # 64*7*7 = 3136
val out = conv_out |> model
```

**E0504: MatMul Incompatible**
```simple
# Error
val A: Tensor<f32, [32, 64]> = ...
val B: Tensor<f32, [128, 256]> = ...
val C = A @ B  # E0504: 64 != 128

# Rule: For A @ B, A's last dim must equal B's second-to-last
# [M, K] @ [K, N] → [M, N]

# Fix: Use correct dimensions
val B: Tensor<f32, [64, 256]> = ...
val C = A @ B  # [32, 64] @ [64, 256] = [32, 256] ✓
```

**E0507: Channel Mismatch**
```simple
# Error
val x: Tensor<f32, [batch, 3, 224, 224]> = ...  # RGB (3 channels)
val conv = Conv2d(1, 32, 3)  # Expects 1 channel!
# E0507: Conv2d expects 1 input channels, got 3

# Fix: Match in_channels
val conv = Conv2d(3, 32, 3)  # 3 input channels ✓
```

---

## Dimension Check Modes

Configure checking behavior for development vs production.

```simple
enum DimCheckMode:
    None_   # No checks (production)
    Assert  # Debug assertions (default)
    Log     # Warn but continue
    Strict  # Return error

# Usage
val ctx = HmInferContext.with_dim_check_mode(DimCheckMode.Assert)
```

---

## Real-World Architecture Examples

### MLP Classifier

```simple
val mlp = Linear(784, 512) ~> ReLU() ~> Dropout(0.2)
      ~> Linear(512, 256) ~> ReLU() ~> Dropout(0.2)
      ~> Linear(256, 10) ~> Softmax()
# Type: Layer<[batch, 784], [batch, 10]>
```

### CNN (ResNet-style)

```simple
val stem = Conv2d(3, 64, 7, stride=2, padding=3) ~> BatchNorm2d(64) ~> ReLU() ~> MaxPool2d(3, stride=2)

val block = Conv2d(64, 64, 3, padding=1) ~> BatchNorm2d(64) ~> ReLU()
        ~> Conv2d(64, 64, 3, padding=1) ~> BatchNorm2d(64)

val classifier = AdaptiveAvgPool2d(1) ~> Flatten() ~> Linear(64, 1000)

val resnet = stem ~> block ~> classifier
```

### Transformer Encoder

```simple
val self_attn = MultiHeadAttention(d_model=512, num_heads=8)
val ffn = Linear(512, 2048) ~> ReLU() ~> Linear(2048, 512)

# Encoder layer with residual connections handled internally
val encoder_layer = LayerNorm(512) ~> self_attn ~> LayerNorm(512) ~> ffn
# Type: Layer<[batch, seq, 512], [batch, seq, 512]>

# Stack 6 layers
val encoder = encoder_layer ~> encoder_layer ~> encoder_layer
          ~> encoder_layer ~> encoder_layer ~> encoder_layer
```

### Autoencoder

```simple
val encoder = Linear(784, 256) ~> ReLU() ~> Linear(256, 64) ~> ReLU() ~> Linear(64, 16)
val decoder = Linear(16, 64) ~> ReLU() ~> Linear(64, 256) ~> ReLU() ~> Linear(256, 784)
val autoencoder = encoder ~> decoder
# Type: Layer<[batch, 784], [batch, 784]>
```

---

## Debugging Dimension Errors

### 1. Print Shapes

```simple
print "Input shape: {x.shape}"
print "After conv: {conv_out.shape}"
print "After flatten: {flat.shape}"
```

### 2. Use Explicit Types

```simple
# Add type annotations to catch errors early
val encoder: Layer<[batch, 784], [batch, 64]> = ...
val decoder: Layer<[batch, 64], [batch, 784]> = ...
```

### 3. Check Common Pitfalls

| Mistake | Fix |
|---------|-----|
| Forgot `Flatten()` before Linear | Add `Flatten()` layer |
| Wrong `in_channels` in Conv | Match to previous layer's `out_channels` |
| Batch dim in wrong position | Use `NCHW` or `NHWC` consistently |
| Kernel too large | Add padding or use smaller kernel |

---

## Best Practices for Dimension Checking

### 1. Use `~>` for Neural Networks

✅ **DO**: Dimension-checked pipeline
```simple
val model = Linear(784, 256) ~> ReLU() ~> Linear(256, 10)
```

❌ **DON'T**: Manual forward calls
```simple
fn forward(x):
    var h = self.linear1(x)
    h = self.relu(h)
    self.linear2(h)
```

### 2. Use `|>` for Data Transformations

✅ **DO**: Clear data flow
```simple
val result = raw_data |> preprocess |> validate |> transform
```

❌ **DON'T**: Nested calls
```simple
val result = transform(validate(preprocess(raw_data)))
```

### 3. Use `>>` for Reusable Pipelines

✅ **DO**: Composable, reusable
```simple
val preprocess = normalize >> augment >> to_tensor
val train_data = load_data() |> preprocess
val test_data = load_test() |> preprocess
```

### 4. Add Type Annotations for Clarity

```simple
# Explicit layer types help catch errors early
val encoder: Layer<[batch, 784], [batch, 64]> =
    Linear(784, 256) ~> ReLU() ~> Linear(256, 64)
```

---

## Related Documentation

- **Design Document**: `doc/design/pipeline_operators_design.md`
- **Error Guide**: `doc/guide/dimension_errors_guide.md`
- **Syntax Reference**: `doc/guide/syntax_quick_reference.md`
- **Test Specs**: `src/compiler/test/dim_constraints_spec.spl`

---

## See Also

- `/coding` - Simple language coding standards
- `/test` - Writing tests in Simple
- `/design` - API design patterns
- `/stdlib` - Standard library modules
