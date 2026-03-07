# Deep Learning

**Version:** 0.5.0
**Status:** Production (Pure Simple), Development (PyTorch FFI)

---

## Overview

Simple provides deep learning capabilities through two approaches:

- **Pure Simple** -- Neural networks written entirely in Simple (tensors, autograd, layers, training)
- **PyTorch FFI** -- Accelerate computation by calling PyTorch/LibTorch via FFI

Both can be mixed: use Pure Simple for small models or prototyping, switch to PyTorch FFI for production-scale training.

---

## Quick Start: Pure Simple Neural Network

```simple
use std.ml.{Tensor, Linear, relu, cross_entropy_loss, SGD}

fn main():
    # Define layers
    val layer1 = Linear(in_features: 784, out_features: 256)
    val layer2 = Linear(in_features: 256, out_features: 10)

    # Forward pass
    val input = Tensor.random(batch_size: 32, features: 784)
    val hidden = relu(layer1.forward(input))
    val output = layer2.forward(hidden)

    # Loss and backward
    val target = Tensor.one_hot(labels, num_classes: 10)
    val loss = cross_entropy_loss(output, target)
    loss.backward()

    # Update weights
    val optimizer = SGD(lr: 0.01)
    optimizer.step([layer1, layer2])
```

---

## Pure Simple Components

### Tensors

```simple
use std.ml.{Tensor}

# Create tensors
val zeros = Tensor.zeros(3, 4)
val ones = Tensor.ones(3, 4)
val random = Tensor.random(3, 4)
val from_data = Tensor.from_list([[1.0, 2.0], [3.0, 4.0]])

# Operations
val sum = a + b              # Element-wise add
val product = a * b          # Element-wise multiply
val matmul = a.matmul(b)     # Matrix multiplication
val transposed = a.transpose()
val reshaped = a.reshape(6, 2)
```

### Autograd

```simple
use std.ml.{Tensor, requires_grad}

# Enable gradient tracking
val x = Tensor.from_list([2.0, 3.0]).requires_grad(true)
val y = x * x + x * 3.0      # y = x^2 + 3x

# Compute gradients
y.sum().backward()
print "dy/dx = {x.grad}"      # [7.0, 9.0] (2x + 3)
```

### Layers

| Layer | Constructor | Description |
|-------|------------|-------------|
| `Linear` | `Linear(in, out)` | Fully connected layer |
| `Conv2d` | `Conv2d(in_ch, out_ch, kernel)` | 2D convolution |
| `BatchNorm` | `BatchNorm(features)` | Batch normalization |
| `Dropout` | `Dropout(rate: 0.5)` | Dropout regularization |
| `LSTM` | `LSTM(input_size, hidden_size)` | LSTM recurrent layer |
| `Embedding` | `Embedding(vocab, dim)` | Word embedding lookup |

### Activation Functions

```simple
use std.ml.{relu, sigmoid, tanh, softmax, gelu}

val h = relu(x)         # max(0, x)
val h = sigmoid(x)      # 1 / (1 + exp(-x))
val h = tanh(x)         # Hyperbolic tangent
val h = softmax(x)      # Normalized probabilities
val h = gelu(x)         # Gaussian Error Linear Unit
```

### Loss Functions

```simple
use std.ml.{cross_entropy_loss, mse_loss, binary_cross_entropy}

val loss = cross_entropy_loss(predicted, target)
val loss = mse_loss(predicted, target)
val loss = binary_cross_entropy(predicted, target)
```

### Optimizers

```simple
use std.ml.{SGD, Adam, AdamW}

val sgd = SGD(lr: 0.01, momentum: 0.9)
val adam = Adam(lr: 0.001, beta1: 0.9, beta2: 0.999)
val adamw = AdamW(lr: 0.001, weight_decay: 0.01)

# Training step
optimizer.zero_grad()
val loss = compute_loss(model, batch)
loss.backward()
optimizer.step(model.parameters())
```

---

## Training Loop

### Basic Pattern

```simple
use std.ml.{Tensor, Linear, relu, cross_entropy_loss, Adam, DataLoader}

fn train(model: Model, train_data: DataLoader, epochs: i64):
    val optimizer = Adam(lr: 0.001)

    for epoch in 0..epochs:
        var total_loss = 0.0
        var num_batches = 0

        for batch in train_data:
            # Forward
            val output = model.forward(batch.input)
            val loss = cross_entropy_loss(output, batch.target)

            # Backward
            optimizer.zero_grad()
            loss.backward()
            optimizer.step(model.parameters())

            total_loss = total_loss + loss.item()
            num_batches = num_batches + 1

        print "Epoch {epoch + 1}: loss = {total_loss / num_batches}"
```

### With Validation

```simple
fn train_with_validation(model: Model, train_data: DataLoader, val_data: DataLoader, epochs: i64):
    val optimizer = Adam(lr: 0.001)
    var best_val_loss = 1e10

    for epoch in 0..epochs:
        # Training phase
        model.train()
        for batch in train_data:
            val output = model.forward(batch.input)
            val loss = cross_entropy_loss(output, batch.target)
            optimizer.zero_grad()
            loss.backward()
            optimizer.step(model.parameters())

        # Validation phase
        model.eval()
        var val_loss = 0.0
        var correct = 0
        var total = 0
        for batch in val_data:
            val output = model.forward(batch.input)
            val loss = cross_entropy_loss(output, batch.target)
            val_loss = val_loss + loss.item()
            correct = correct + count_correct(output, batch.target)
            total = total + batch.target.size(0)

        val accuracy = correct / total
        print "Epoch {epoch + 1}: val_loss={val_loss}, accuracy={accuracy}"

        if val_loss < best_val_loss:
            best_val_loss = val_loss
            model.save("best_model.sdn")
```

---

## PyTorch FFI Integration

### Setup

```bash
# Check status
bin/simple pytorch-status

# CPU mode (always works)
bin/simple build --features=pytorch-cpu

# CUDA mode (requires LibTorch with CUDA)
export LIBTORCH_PATH=/path/to/libtorch
bin/simple build --features=pytorch-cuda
```

### API

```simple
use std.torch.{Tensor as TorchTensor, cuda_available}

fn main():
    if cuda_available():
        print "CUDA available, using GPU"

    val t = TorchTensor.zeros(100, 100)
    val result = t.matmul(t.transpose(0, 1))
    print "Result shape: {result.shape()}"
```

### PyTorch CUDA Setup

| Mode | LibTorch Build | Environment |
|------|---------------|-------------|
| CPU | `libtorch-cxx11-abi-shared-with-deps` | `LIBTORCH_USE_CUDA=0` |
| CUDA | `libtorch-cxx11-abi-shared-with-deps+cu118` | `LIBTORCH_USE_CUDA=1` |

**Switching modes:**
```bash
# CPU mode
export LIBTORCH_USE_CUDA=0

# CUDA mode
export LIBTORCH_USE_CUDA=1
export CUDA_HOME=/usr/local/cuda
```

### Current Limitations

- CPU mode: fully functional
- CUDA mode: requires matching LibTorch + CUDA toolkit versions
- `.as_ptr()` on List types not yet supported for direct FFI

---

## Acceleration Configuration

### Modes

| Mode | Description | When to Use |
|------|-------------|-------------|
| **PureSimple** | All computation in Simple | Prototyping, education, small models |
| **PyTorchFFI** | Delegate to PyTorch | Production training, large models |
| **Auto** | Automatic selection | Default -- best of both |

### Configuration

```sdn
# acceleration.sdn
acceleration:
    mode: "auto"
    threshold: 1000
    profiling: false
    pytorch_path: "/usr/lib/libtorch"
```

### Auto Mode Thresholds

Operations below the threshold use PureSimple; above use PyTorchFFI:

| Operation | Default Threshold |
|-----------|------------------|
| Matrix multiply | 1000 elements |
| Convolution | 1000 elements |
| Element-wise ops | Always PureSimple |
| Reduction | 10000 elements |

### Performance Expectations

| Operation (1000x1000 matrix) | PureSimple | PyTorchFFI (CPU) | PyTorchFFI (CUDA) |
|------------------------------|-----------|-----------------|-------------------|
| MatMul | ~500ms | ~50ms | ~2ms |
| Element-wise add | ~10ms | ~5ms | ~0.5ms |
| Softmax | ~20ms | ~8ms | ~1ms |
| Conv2d (3x3) | ~200ms | ~15ms | ~1ms |

---

## Training Infrastructure

### Configuration System

```simple
use std.ml.config.{TrainConfig, ModelConfig, DataConfig}

val config = TrainConfig(
    model: ModelConfig(
        name: "my_model",
        layers: [256, 128, 64, 10],
        dropout: 0.3,
        activation: "relu"
    ),
    data: DataConfig(
        train_path: "data/train",
        val_path: "data/val",
        batch_size: 32,
        shuffle: true
    ),
    epochs: 100,
    learning_rate: 0.001,
    optimizer: "adam",
    early_stopping: 10
)
```

### Experiment Tracking

```simple
use std.ml.tracking.{Experiment}

val exp = Experiment.create("mnist_classifier")

for epoch in 0..config.epochs:
    val train_loss = train_epoch(model, train_data, optimizer)
    val val_loss = validate(model, val_data)

    exp.log_metric("train_loss", train_loss, step: epoch)
    exp.log_metric("val_loss", val_loss, step: epoch)
    exp.log_metric("learning_rate", optimizer.lr, step: epoch)

exp.save_model(model, "final_model")
exp.finish()
```

### Training Engine

PyTorch Ignite-style training engine for structured training loops:

```simple
use std.ml.engine.{TrainingEngine, Events}

val engine = TrainingEngine(model, optimizer, loss_fn)

engine.on(Events.EPOCH_COMPLETED, fn(state):
    print "Epoch {state.epoch}: loss={state.output}"
)

engine.on(Events.COMPLETED, fn(state):
    print "Training complete!"
    model.save("trained_model.sdn")
)

engine.run(train_data, max_epochs: 100)
```

### Metrics

```simple
use std.ml.metrics.{Accuracy, Precision, Recall, F1Score}

val accuracy = Accuracy()
val f1 = F1Score(average: "macro")

for batch in val_data:
    val output = model.forward(batch.input)
    val predictions = output.argmax(dim: 1)
    accuracy.update(predictions, batch.target)
    f1.update(predictions, batch.target)

print "Accuracy: {accuracy.compute()}"
print "F1 Score: {f1.compute()}"
```

---

## Progressive LoRA Training

Fine-tune large language models efficiently using Low-Rank Adaptation:

```simple
use std.ml.lora.{LoRAConfig, apply_lora, merge_lora}

# Configure LoRA
val lora_config = LoRAConfig(
    rank: 8,
    alpha: 16,
    target_modules: ["q_proj", "v_proj"],
    dropout: 0.05
)

# Apply LoRA to base model
val model = load_model("base_model.sdn")
val lora_model = apply_lora(model, lora_config)

# Train only LoRA parameters (much fewer than full model)
val optimizer = Adam(lr: 1e-4)
for epoch in 0..epochs:
    for batch in train_data:
        val output = lora_model.forward(batch.input)
        val loss = cross_entropy_loss(output, batch.target)
        optimizer.zero_grad()
        loss.backward()
        optimizer.step(lora_model.lora_parameters())

# Merge LoRA weights back into base model
val final_model = merge_lora(lora_model)
final_model.save("finetuned_model.sdn")
```

### Progressive Training Phases

| Phase | LoRA Rank | Learning Rate | Purpose |
|-------|-----------|---------------|---------|
| 1: Warm-up | 4 | 1e-4 | Initial adaptation |
| 2: Core | 8 | 5e-5 | Main training |
| 3: Refinement | 16 | 1e-5 | Fine-grained tuning |

---

## Model Examples

### MNIST Classifier

```simple
class MnistClassifier:
    fc1: Linear
    fc2: Linear
    fc3: Linear

    static fn create() -> MnistClassifier:
        MnistClassifier(
            fc1: Linear(784, 256),
            fc2: Linear(256, 128),
            fc3: Linear(128, 10)
        )

    fn forward(x: Tensor) -> Tensor:
        var h = relu(self.fc1.forward(x))
        h = relu(self.fc2.forward(h))
        self.fc3.forward(h)

    fn parameters() -> List<Tensor>:
        self.fc1.parameters() + self.fc2.parameters() + self.fc3.parameters()
```

### Transformer Block

```simple
class TransformerBlock:
    attention: MultiHeadAttention
    ffn: FeedForward
    norm1: LayerNorm
    norm2: LayerNorm

    fn forward(x: Tensor) -> Tensor:
        # Self-attention with residual
        val attn_out = self.attention.forward(x, x, x)
        var h = self.norm1.forward(x + attn_out)

        # Feed-forward with residual
        val ffn_out = self.ffn.forward(h)
        self.norm2.forward(h + ffn_out)
```

---

## Best Practices

1. **Start with PureSimple** -- Verify correctness before switching to PyTorchFFI
2. **Use Auto mode** -- Let the runtime choose the best execution path
3. **Monitor memory** -- Use `Tensor.memory_usage()` to track allocations
4. **Validate shapes** -- Use tensor dimension inference (see `doc/guide/deep_learning/tensor_dimensions.md`)
5. **Save checkpoints** -- Save model state every N epochs for recovery
6. **Use experiment tracking** -- Log all metrics for reproducibility
7. **Start with small models** -- Scale up after confirming the pipeline works

---

## Troubleshooting

| Issue | Cause | Fix |
|-------|-------|-----|
| Gradient is nil | `requires_grad` not set | Call `.requires_grad(true)` on input tensors |
| NaN loss | Learning rate too high | Reduce learning rate by 10x |
| Out of memory | Batch size too large | Reduce batch size or use gradient accumulation |
| PyTorch not found | LibTorch not installed | Set `LIBTORCH_PATH` environment variable |
| CUDA error | GPU driver mismatch | Match CUDA toolkit to driver version |
| Slow training | Using PureSimple for large ops | Switch to `mode: "auto"` or `"pytorch_ffi"` |
| Model not converging | Architecture issue | Check layer dimensions, try different optimizer |

---

## Related Documentation

- Tensor dimensions: `doc/guide/deep_learning/tensor_dimensions.md`
- GPU programming: `doc/guide/backend/gpu_programming.md`
- SFFI (for PyTorch FFI): `doc/guide/ffi/sffi.md`
