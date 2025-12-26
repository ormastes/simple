# PyTorch Integration Implementation Plan

**Created:** 2025-12-26
**Status:** Planning
**Priority:** High (Foundational for ML/AI work)
**Approach:** LibTorch C++ API first, Python bridge for ecosystem

## Overview

Implement comprehensive PyTorch integration for Simple language, enabling machine learning and deep learning applications. Use LibTorch (C++ API) as primary interface for performance, with Python bridge for ecosystem access (pretrained models, datasets). Leverage Simple's type system for better safety than Python PyTorch.

## Goals

1. Provide complete PyTorch functionality in type-safe Simple
2. Match or exceed Python PyTorch performance
3. Enable zero-copy tensor sharing with Python ecosystem
4. Support distributed training and inference
5. Leverage Simple's unique features (effects, actors, units)

## Phase 1: LibTorch Core (3 months)

### Month 1: FFI Bindings & Tensors

**Week 1-2: Build System & LibTorch Linking**
- [ ] Download and integrate LibTorch C++ library
- [ ] Setup CMake/build integration
- [ ] Link libtorch, libc10, libaten
- [ ] Test basic tensor creation from C++

**Week 3-4: Tensor Operations FFI**
- [ ] Generate FFI bindings for 100+ tensor operations
- [ ] Tensor creation (zeros, ones, randn, etc.)
- [ ] Element-wise operations (+, -, *, /, etc.)
- [ ] Reductions (sum, mean, max, etc.)
- [ ] Indexing and slicing

**Deliverable:** `simple/std_lib/src/ml/torch/ffi.spl` with core tensor operations

### Month 2: Autograd System

**Week 1-2: Gradient Tracking**
- [ ] Enable `requires_grad` on tensors
- [ ] Implement `backward()` function
- [ ] Gradient accumulation
- [ ] Access `.grad()` property

**Week 3-4: Custom Autograd Functions**
- [ ] Context for save_for_backward
- [ ] Custom forward/backward functions
- [ ] Integration with Simple's type system
- [ ] Gradient checkpointing

**Deliverable:** Working autograd with custom functions

### Month 3: Neural Network Modules

**Week 1-2: Module System**
- [ ] `Module` trait design
- [ ] Parameter management
- [ ] Forward function abstraction
- [ ] Train/eval modes

**Week 3-4: Core Modules**
- [ ] Linear (fully connected) layer
- [ ] Conv2d, Conv3d
- [ ] RNN, LSTM, GRU
- [ ] BatchNorm, LayerNorm
- [ ] Dropout, Embedding
- [ ] Sequential container

**Deliverable:** Neural network library with 20+ modules

## Phase 2: Training Infrastructure (2 months)

### Month 4: Optimizers & Data Loading

**Week 1-2: Optimizers**
- [ ] SGD (with momentum)
- [ ] Adam, AdamW
- [ ] RMSprop
- [ ] Learning rate schedulers (StepLR, ExponentialLR, CosineAnnealing)

**Week 3-4: Data Loading**
- [ ] Dataset trait
- [ ] DataLoader (batching, shuffling, parallel loading)
- [ ] Common datasets (MNIST, CIFAR-10, ImageNet)
- [ ] Data augmentation transforms

**Deliverable:** Complete training loop infrastructure

### Month 5: Loss Functions & Metrics

**Week 1-2: Loss Functions**
- [ ] MSE Loss
- [ ] Cross Entropy Loss
- [ ] NLL Loss
- [ ] BCE Loss
- [ ] Custom loss functions

**Week 3-4: Metrics & Utilities**
- [ ] Accuracy, Precision, Recall, F1
- [ ] Model checkpointing
- [ ] Early stopping
- [ ] TensorBoard logging

**Deliverable:** Complete ML utilities module

## Phase 3: Python Bridge (1 month)

### Month 6: Python Interop & Ecosystem

**Week 1-2: CPython Embedding**
- [ ] Initialize Python interpreter in Simple
- [ ] Call Python functions from Simple
- [ ] Handle GIL properly
- [ ] Exception handling and error propagation

**Week 3: DLPack Zero-Copy**
- [ ] Implement DLPack export/import
- [ ] Simple Tensor → PyTorch Tensor (zero-copy)
- [ ] PyTorch Tensor → Simple Tensor (zero-copy)
- [ ] Validate no memory copies on GPU

**Week 4: Ecosystem Integration**
- [ ] Load pretrained models from Python
- [ ] Use torchvision, transformers libraries
- [ ] Export models to ONNX
- [ ] Model zoo access

**Deliverable:** Seamless Python ecosystem integration

## Phase 4: Advanced Features (3 months)

### Month 7: Distributed Training

**Week 1-2: Multi-GPU Support**
- [ ] Data parallelism (DistributedDataParallel)
- [ ] Model parallelism
- [ ] Gradient synchronization (all-reduce)
- [ ] NCCL backend integration

**Week 3-4: Distributed Infrastructure**
- [ ] Process group initialization
- [ ] Rank and world size management
- [ ] Distributed sampling
- [ ] Checkpointing for distributed training

**Deliverable:** Multi-GPU training working

### Month 8: Mixed Precision & Optimization

**Week 1-2: Automatic Mixed Precision (AMP)**
- [ ] Autocast context for FP16/BF16
- [ ] GradScaler for loss scaling
- [ ] Dynamic loss scaling
- [ ] Performance benchmarking

**Week 3-4: Performance Optimization**
- [ ] Kernel fusion opportunities
- [ ] Memory pooling
- [ ] Async data loading
- [ ] Profile and optimize hot paths

**Deliverable:** AMP working, 2x speedup on large models

### Month 9: Custom Kernels & Deployment

**Week 1-2: Custom CUDA Kernels**
- [ ] Integrate Simple's CUDA support
- [ ] Custom kernel in autograd
- [ ] Vulkan compute shaders (alternative)
- [ ] Performance comparison

**Week 3-4: TorchScript & Deployment**
- [ ] Export Simple models to TorchScript
- [ ] JIT compilation
- [ ] Mobile deployment
- [ ] ONNX export/import

**Deliverable:** Custom kernel integration, model deployment pipeline

## Technical Architecture

### Module Structure

```
simple/std_lib/src/ml/
├── torch/                    # PyTorch bindings
│   ├── __init__.spl
│   ├── ffi.spl               # Low-level FFI to LibTorch
│   ├── tensor.spl            # Tensor type and operations
│   ├── autograd.spl          # Autograd engine
│   ├── nn/                   # Neural network modules
│   │   ├── __init__.spl
│   │   ├── module.spl        # Module trait
│   │   ├── linear.spl
│   │   ├── conv.spl
│   │   ├── rnn.spl
│   │   ├── normalization.spl
│   │   └── activation.spl
│   ├── optim/                # Optimizers
│   │   ├── __init__.spl
│   │   ├── optimizer.spl     # Optimizer trait
│   │   ├── sgd.spl
│   │   ├── adam.spl
│   │   └── scheduler.spl
│   ├── data/                 # Data loading
│   │   ├── __init__.spl
│   │   ├── dataset.spl
│   │   ├── dataloader.spl
│   │   └── transforms.spl
│   ├── distributed/          # Distributed training
│   │   ├── __init__.spl
│   │   ├── ddp.spl
│   │   └── nccl.spl
│   ├── amp/                  # Mixed precision
│   │   ├── __init__.spl
│   │   └── autocast.spl
│   └── utils/                # Utilities
│       ├── checkpoint.spl
│       ├── tensorboard.spl
│       └── metrics.spl
│
└── vision/                   # Computer vision (built on torch)
    ├── __init__.spl
    ├── models/               # Pretrained models
    │   ├── resnet.spl
    │   ├── vgg.spl
    │   └── transformer.spl
    └── transforms.spl        # Image transformations
```

### Tensor Type Design

```simple
# Type-safe tensors with optional shape tracking
struct Tensor<T, Shape = DynamicShape>:
    ptr: *Void  # Pointer to torch::Tensor
    phantom: PhantomData<(T, Shape)>

# Factory functions
fn zeros<T>(shape: Array<Int>) -> Tensor<T>
fn randn<T>(shape: Array<Int>) -> Tensor<T>
fn from_array<T>(data: Array<T>, shape: Array<Int>) -> Tensor<T>

# Operations (type-safe)
fn add<T>(a: Tensor<T>, b: Tensor<T>) -> Tensor<T>
fn matmul<T>(a: Tensor<T>, b: Tensor<T>) -> Tensor<T>

# Optional static shape checking
type ImageBatch = Tensor<Float32, [Batch, 3, 224, 224]>
type WeightMatrix = Tensor<Float32, [InFeatures, OutFeatures]>
```

### Module System

```simple
# Module trait
trait Module<Input, Output>:
    fn forward(self: mut Self, input: Input) -> Output
    fn parameters(self: Self) -> Array<Tensor<Float32>>
    fn train(self: mut Self)
    fn eval(self: mut Self)

# Example: Linear layer
class Linear(Module<Tensor<Float32>, Tensor<Float32>>):
    weight: Tensor<Float32>
    bias: Option<Tensor<Float32>>

    fn init(in_features: Int, out_features: Int, bias: Bool = true):
        self.weight = torch.randn([out_features, in_features])
        self.bias = if bias { Some(torch.zeros([out_features])) } else { None }

    fn forward(input: Tensor<Float32>) -> Tensor<Float32>:
        output = input.matmul(self.weight.t())
        if let Some(b) = self.bias:
            output = output + b
        return output

    fn parameters() -> Array<Tensor<Float32>>:
        match self.bias:
            Some(b) => [self.weight, b]
            None => [self.weight]
```

### Training Loop

```simple
import simple.ml.torch as torch

# Create model
let model = NeuralNet()

# Create optimizer
let optimizer = torch.optim.Adam(model.parameters(), lr: 0.001)

# Create data loader
let train_loader = torch.data.DataLoader(train_dataset, batch_size: 64)

# Training loop
fn train_epoch(epoch: Int):
    model.train()

    for batch_idx, (data, target) in train_loader.enumerate():
        # Zero gradients
        optimizer.zero_grad()

        # Forward pass
        output = model.forward(data)
        loss = torch.nn.cross_entropy(output, target)

        # Backward pass
        loss.backward()

        # Update weights
        optimizer.step()

        if batch_idx % 100 == 0:
            print(f"Epoch {epoch}, Batch {batch_idx}, Loss: {loss.item()}")

# Train
for epoch in 1..11:
    train_epoch(epoch)
```

## Dependencies

### External Libraries
- **LibTorch:** PyTorch C++ library (download from pytorch.org)
- **CPython:** Python 3.10+ development headers (for Python bridge)
- **CUDA:** NVIDIA CUDA Toolkit (for GPU support)
- **cuDNN:** NVIDIA cuDNN library (for accelerated ops)

### Simple Compiler Features Required
- ✅ FFI support
- ✅ Trait system
- ✅ Generic types
- ✅ GPU/CUDA support (for custom kernels)
- ⏳ Python interop (new)

## Success Metrics

### Performance
- [ ] Match Python PyTorch performance (within 5%)
- [ ] FFI overhead < 1% for large operations
- [ ] DLPack zero-copy working
- [ ] Training throughput comparable to Python

### Usability
- [ ] Developer can define and train model in < 10 minutes
- [ ] API feels natural to PyTorch users
- [ ] Type safety prevents common bugs

### Safety
- [ ] Tensor shape mismatches caught at compile-time (when using static shapes)
- [ ] No memory leaks in training loops
- [ ] GPU memory managed safely

### Ecosystem
- [ ] Can load pretrained models from PyTorch Hub
- [ ] Interoperability with torchvision, transformers
- [ ] Export to ONNX working

## Risks & Mitigations

### Risk: LibTorch API Instability
**Mitigation:** Pin to specific LibTorch version, maintain compatibility matrix, version-specific bindings

### Risk: Python Overhead
**Mitigation:** Use LibTorch directly for core operations, Python only for ecosystem access

### Risk: Complex Tensor Memory Management
**Mitigation:** Explicit ownership model, automatic cleanup via RAII, extensive testing

### Risk: Limited Type-Level Shape Checking
**Mitigation:** Provide optional static shapes, runtime checks with clear errors, gradual typing

## Future Enhancements (Post-Release)

- [ ] Additional backends (MPS for Apple Silicon, ROCm for AMD)
- [ ] Quantization (INT8, mixed precision)
- [ ] Pruning and compression
- [ ] Neural architecture search (NAS)
- [ ] Hyperparameter optimization
- [ ] Model interpretability tools (GradCAM, attention viz)
- [ ] Reinforcement learning algorithms (PPO, SAC, etc.)
- [ ] Graph neural networks
- [ ] Transformers library port
- [ ] Diffusion models support

## Example Applications

### 1. Image Classification

```simple
import simple.ml.torch as torch
import simple.ml.vision as vision

# Load pretrained model
let model = vision.models.resnet50(pretrained: true)
model.eval()

# Preprocess image
let image = vision.io.read_image("cat.jpg")
let preprocessed = vision.transforms.compose([
    vision.transforms.Resize(256),
    vision.transforms.CenterCrop(224),
    vision.transforms.ToTensor(),
    vision.transforms.Normalize(mean: [0.485, 0.456, 0.406], std: [0.229, 0.224, 0.225])
])(image)

# Inference
let output = model.forward(preprocessed.unsqueeze(0))
let predicted_class = output.argmax(dim: 1)
print(f"Predicted: {class_names[predicted_class]}")
```

### 2. Text Generation (GPT-style)

```simple
import simple.ml.torch as torch

# Transformer model
class GPT(torch.nn.Module):
    embedding: torch.nn.Embedding
    transformer_blocks: Array<TransformerBlock>
    ln_f: torch.nn.LayerNorm
    head: torch.nn.Linear

    fn forward(input_ids: Tensor<Int64>) -> Tensor<Float32>:
        x = self.embedding.forward(input_ids)

        for block in self.transformer_blocks:
            x = block.forward(x)

        x = self.ln_f.forward(x)
        logits = self.head.forward(x)

        return logits

# Generate text
fn generate(model: GPT, prompt: String, max_length: Int) -> String:
    tokens = tokenize(prompt)

    for _ in 0..max_length:
        logits = model.forward(tokens)
        next_token = logits[:, -1, :].argmax(dim: 1)
        tokens = torch.cat([tokens, next_token.unsqueeze(0)], dim: 1)

        if next_token == EOS_TOKEN:
            break

    return detokenize(tokens)
```

### 3. Reinforcement Learning

```simple
import simple.ml.torch as torch
import simple.physics.isaac as isaac  # Integration with physics engines!

# Policy network
class PolicyNetwork(torch.nn.Module):
    fc1: torch.nn.Linear
    fc2: torch.nn.Linear
    action_head: torch.nn.Linear
    value_head: torch.nn.Linear

    fn forward(state: Tensor<Float32>) -> (Tensor<Float32>, Tensor<Float32>):
        x = torch.relu(self.fc1.forward(state))
        x = torch.relu(self.fc2.forward(state))

        action_logits = self.action_head.forward(x)
        state_value = self.value_head.forward(x)

        return (action_logits, state_value)

# PPO training
let env = isaac.make_env("Humanoid-v0", num_envs: 2048)
let policy = PolicyNetwork()
let optimizer = torch.optim.Adam(policy.parameters(), lr: 0.0003)

for iteration in 0..1000:
    # Collect rollouts
    states, actions, rewards, dones = collect_rollouts(env, policy, num_steps: 128)

    # Compute advantages
    advantages = compute_gae(rewards, dones, gamma: 0.99, lambda: 0.95)

    # Update policy
    for epoch in 0..10:
        action_logits, values = policy.forward(states)
        loss = ppo_loss(action_logits, actions, advantages, values)

        optimizer.zero_grad()
        loss.backward()
        optimizer.step()
```

## Integration with Other Categories

### With Game Engines
```simple
# Use PyTorch for AI in games
import simple.godot as godot
import simple.ml.torch as torch

class AIController(godot.Node):
    policy: torch.nn.Module

    fn _ready():
        # Load pretrained policy
        self.policy = torch.load("agent_policy.pt")
        self.policy.eval()

    fn _process(delta: #Duration):
        # Get game state
        state = get_game_state()

        # Run policy
        with torch.no_grad():
            action = self.policy.forward(state).argmax()

        # Execute action in game
        execute_action(action)
```

### With Physics Engines
```simple
# Train RL agent with physics simulation
import simple.physics.isaac as isaac
import simple.ml.torch as torch

# Environment provides observations as Simple tensors
let env = isaac.make_env("Franka-v0", num_envs: 1024)

# Policy is PyTorch neural network
let policy = torch.nn.Sequential([
    torch.nn.Linear(37, 128),
    torch.nn.ReLU(),
    torch.nn.Linear(128, 8)
])

# Training loop (both systems work together seamlessly)
let obs = env.reset()  # Simple Tensor (from physics)
let actions = policy.forward(obs)  # PyTorch forward pass
env.step(actions)  # Back to physics simulation
```

## References

- Research: `doc/research/pytorch_integration.md`
- LibTorch Docs: https://pytorch.org/cppdocs/
- PyTorch C++ API: https://pytorch.org/tutorials/advanced/cpp_frontend.html
- DLPack Spec: https://github.com/dmlc/dlpack
- TorchScript: https://pytorch.org/docs/stable/jit.html
