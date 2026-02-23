# Deep Learning in Simple - Quickstart Tutorial

**Target Audience**: Developers new to Simple language or deep learning
**Time Required**: 2-3 hours
**Prerequisites**: Basic programming knowledge
**Status**: Production Ready (2026-02-16)

---

## Table of Contents

1. [Introduction](#introduction)
2. [Setup](#setup)
3. [Lesson 1: Your First Tensors](#lesson-1-your-first-tensors)
4. [Lesson 2: Neural Network Forward Pass](#lesson-2-neural-network-forward-pass)
5. [Lesson 3: Understanding Gradients](#lesson-3-understanding-gradients)
6. [Lesson 4: Training Your First Model](#lesson-4-training-your-first-model)
7. [Lesson 5: Real Gradient Descent](#lesson-5-real-gradient-descent)
8. [Lesson 6: Building Modular Networks](#lesson-6-building-modular-networks)
9. [Lesson 7: Data Preprocessing](#lesson-7-data-preprocessing)
10. [Next Steps](#next-steps)

---

## Introduction

Welcome to deep learning in Simple! This tutorial will take you from zero to training neural networks in about 2 hours.

### What You'll Learn

- ✅ Tensor operations (add, multiply, matmul)
- ✅ Neural network architecture (layers, activations)
- ✅ Forward and backward propagation
- ✅ Gradient descent optimization
- ✅ Training loops and loss functions
- ✅ Data preprocessing (shuffle, batch, normalize)

### Why Simple for Deep Learning?

- **Pure implementation**: Understand every line of code
- **No black boxes**: See exactly how neural networks work
- **Runtime compatible**: Edit and run instantly (no compilation)
- **Self-contained**: No complex dependencies to install

---

## Setup

### Prerequisites

You need the Simple language runtime:

```bash
# Check if Simple is installed
which simple

# Should output: /usr/local/bin/simple or similar
```

If not installed, see the main Simple documentation for installation.

### Download Examples

All examples are in the `examples/pure_nn/` directory:

```bash
cd /path/to/simple
ls examples/pure_nn/*_runtime.spl
```

You should see:
- `xor_example.spl`
- `autograd_example_runtime.spl`
- `complete_demo_runtime.spl`
- `xor_training_runtime.spl`
- `simple_regression_runtime.spl`
- `nn_layers_runtime.spl`
- `data_utils_runtime.spl`

---

## Lesson 1: Your First Tensors

**Goal**: Understand tensor basics and matrix operations
**Time**: 15 minutes
**File**: `examples/pure_nn/xor_example.spl`

### Run the Example

```bash
bin/simple examples/pure_nn/xor_example.spl
```

### Expected Output

```
=== Pure Simple Deep Learning - XOR Problem ===

Input X shape: [4, 2]
  data: [0, 0, 0, 1, 1, 0, 1, 1]

Weight W shape: [2, 2]
  data: [0.5, 0.3, -0.2, 0.7]

After matmul (X @ W):
  Z shape: [4, 2]
  ...

✓ Pure Simple tensor operations working!
```

### Key Concepts

1. **Tensors are arrays with shapes**:
   ```simple
   class SimpleTensor:
       data: [f64]      # Flat array of values
       shape: [i64]     # Dimensions [rows, cols]
   ```

2. **Matrix multiplication**:
   - `X (4x2) @ W (2x2) = Z (4x2)`
   - Inner dimensions must match: X cols = W rows

3. **Activations transform values**:
   - ReLU: `max(0, x)` - zeros out negatives
   - Used to add non-linearity

### Exercise 1.1

Modify `xor_example.spl` to use a 3x3 weight matrix:

```simple
# Change line ~54:
val w = create_tensor([
    0.5, 0.3, 0.1,
    -0.2, 0.7, 0.4,
    0.6, -0.1, 0.8
], [2, 3])  # Now 2x3 instead of 2x2
```

**Question**: What shape is the output Z now?
**Answer**: `[4, 3]` because `(4x2) @ (2x3) = (4x3)`

---

## Lesson 2: Neural Network Forward Pass

**Goal**: Build and run a multi-layer neural network
**Time**: 20 minutes
**File**: `examples/pure_nn/complete_demo_runtime.spl`

### Run the Example

```bash
bin/simple examples/pure_nn/complete_demo_runtime.spl
```

### Expected Output

```
━━━ Demo 3: Neural Network (2 → 4 → 1) ━━━

Network architecture:
  Input layer: 2 neurons
  Hidden layer: 4 neurons (ReLU activation)
  Output layer: 1 neuron (Sigmoid activation)

Testing on XOR inputs:
Predictions (before training) (4x1):
  [0.5]
  [0.5768852611327774]
  [0.5349429451582147]
  [0.6271477664627765]
```

### Key Concepts

1. **Layers process input sequentially**:
   ```
   Input (2) → Hidden (4) → Output (1)
      ↓           ↓            ↓
     W1,b1      ReLU        W2,b2
                           Sigmoid
   ```

2. **Forward pass formula**:
   ```simple
   # Layer 1: Linear + ReLU
   z1 = x @ w1 + b1
   h1 = ReLU(z1)

   # Layer 2: Linear + Sigmoid
   z2 = h1 @ w2 + b2
   output = Sigmoid(z2)
   ```

3. **Random initialization**:
   - Weights start random (small values ~0.1)
   - Before training, predictions are random
   - Training will adjust weights to be correct

### Exercise 2.1

Count the parameters in a 3-layer network:

**Network**: 10 → 8 → 4 → 2

**Calculation**:
- Layer 1: `10 * 8 + 8 = 88` (weights + biases)
- Layer 2: `8 * 4 + 4 = 36`
- Layer 3: `4 * 2 + 2 = 10`
- **Total**: 134 parameters

Verify by running:
```bash
bin/simple examples/pure_nn/nn_layers_runtime.spl
# Look for "Total parameters" output
```

---

## Lesson 3: Understanding Gradients

**Goal**: Learn how backpropagation computes gradients
**Time**: 25 minutes
**File**: `examples/pure_nn/autograd_example_runtime.spl`

### Run the Example

```bash
bin/simple examples/pure_nn/autograd_example_runtime.spl
```

### Expected Output

```
Example 1: Basic operation (y = x * 2)
  x = 3
  y = x * 2 = 6
  Expected: 6.0

Example 4: ReLU activation
  Input: [-2, -1, 0, 1, 2]
  ReLU output: [0, 0, 0, 1, 2]
  Expected: [0.0, 0.0, 0.0, 1.0, 2.0]
```

### Key Concepts

1. **Gradients measure sensitivity**:
   - If `y = 2x`, then `dy/dx = 2`
   - Changing x by 1 changes y by 2

2. **Chain rule for multiple operations**:
   ```
   z = (x + y) * x
   dz/dx = (x + y) + x = 2x + y
   ```

3. **Why gradients matter**:
   - Tell us how to adjust weights
   - Point in direction that reduces loss
   - Foundation of training

### Exercise 3.1

Calculate gradients manually:

```
Given: f(x) = x^2 + 3x + 2
At x = 4:

f(4) = 16 + 12 + 2 = 30
f'(x) = 2x + 3
f'(4) = 8 + 3 = 11

Interpretation: At x=4, increasing x by 1 increases f by ~11
```

---

## Lesson 4: Training Your First Model

**Goal**: Train a neural network on the XOR problem
**Time**: 20 minutes
**File**: `examples/pure_nn/xor_training_runtime.spl`

### Run the Example

```bash
bin/simple examples/pure_nn/xor_training_runtime.spl
```

### Expected Output

```
Training...
  Epoch 1/5: loss = 0.2546583538321858
  Epoch 2/5: loss = 0.2546583538321858
  ...

Final Predictions:
  Output:
    [0] = 0.5498339973124863 (rounded: 1)
    [1] = 0.5805585978227371 (rounded: 1)
```

### Key Concepts

1. **Training loop structure**:
   ```simple
   for epoch in 0..epochs:
       # Forward pass
       predictions = model.forward(X)
       loss = compute_loss(predictions, Y)

       # Backward pass (gradients)
       gradients = compute_gradients(model, X, Y)

       # Update weights
       model.update(gradients, learning_rate)
   ```

2. **Loss measures error**:
   - MSE (Mean Squared Error): `mean((pred - true)^2)`
   - Lower is better
   - Goal: Minimize loss by adjusting weights

3. **Learning rate controls step size**:
   - Too large: Training unstable, diverges
   - Too small: Training very slow
   - Typical range: 0.001 to 0.1

### Exercise 4.1

Experiment with learning rates:

Modify line ~128:
```simple
# Try different values:
update_weights(net, 0.01, learning_rate)  # Very slow
update_weights(net, 0.5, learning_rate)   # Good
update_weights(net, 2.0, learning_rate)   # Too fast, unstable
```

**Question**: Which learning rate gives best results?
**Answer**: 0.1-0.5 typically works best for this problem

---

## Lesson 5: Real Gradient Descent

**Goal**: See real learning with convergence
**Time**: 25 minutes
**File**: `examples/pure_nn/simple_regression_runtime.spl`

### Run the Example

```bash
bin/simple examples/pure_nn/simple_regression_runtime.spl
```

### Expected Output

```
Training...
  Epoch 0: loss=4.135, w=0.21849999999999997, b=0.39
  Epoch 25: loss=0.06023520762822534, w=1.1654776219849978, b=1.4236304892765232
  Epoch 99: loss=0.008194413572534911, w=1.6923710892502553, b=1.1566067539238423

Learned parameters:
  Weight: 1.6923710892502553 (target: 2.0)
  Bias: 1.1566067539238423 (target: 1.0)
```

### Key Concepts

1. **Gradient descent updates**:
   ```simple
   weight_new = weight_old - (learning_rate * gradient)
   ```
   - Gradient points uphill (increases loss)
   - We go opposite direction (downhill)
   - Learning rate scales the step size

2. **Convergence**:
   - Loss decreases: `4.135 → 0.008` (99.8% reduction!)
   - Parameters approach target: `w → 2.0`, `b → 1.0`
   - Learning is working!

3. **Real backpropagation**:
   ```simple
   # Forward: y_pred = w*x + b
   # Error: error = y_pred - y_true
   # Gradients:
   grad_w = 2 * error * x  # How loss changes with w
   grad_b = 2 * error      # How loss changes with b
   ```

### Exercise 5.1

Train to learn `y = 3x + 5`:

Modify lines ~114-115:
```simple
# Change target function:
val data = generate_linear_data(20, 3.0, 5.0, 0.0)
```

**Expected**: `w ≈ 3.0`, `b ≈ 5.0`

---

## Lesson 6: Building Modular Networks

**Goal**: Understand layer composition and architecture design
**Time**: 25 minutes
**File**: `examples/pure_nn/nn_layers_runtime.spl`

### Run the Example

```bash
bin/simple examples/pure_nn/nn_layers_runtime.spl
```

### Expected Output

```
━━━ Example 1: XOR Network (2 → 4 → 1) ━━━

Parameters:
  Layer 1: 12 (2×4 + 4)
  Layer 2: 5 (4×1 + 1)
  Layer 3: 2 (1×1 + 1)
  Total: 19

━━━ Example 4: Activation Functions ━━━

ReLU output:
  [0] = 0
  [1] = 0
  [2] = 0
  [3] = 1
  [4] = 2

Softmax output (normalized to probability distribution):
  [0] = 0.011656232879411442
  [1] = 0.03168492081350819
  [2] = 0.08612854448335461
  [3] = 0.23412165738065918
  [4] = 0.6364086444430666
  Sum: 1
```

### Key Concepts

1. **Layer abstraction**:
   ```simple
   class LinearLayer:
       weight: SimpleTensor
       bias: SimpleTensor

   fn forward(x):
       return x @ weight + bias
   ```

2. **Activation functions**:
   - **ReLU**: For hidden layers (non-linearity)
   - **Sigmoid**: For binary classification (0-1 output)
   - **Softmax**: For multi-class (probability distribution)

3. **Network composition**:
   ```simple
   Network = [
       Linear(10, 8),
       ReLU(),
       Linear(8, 3),
       Softmax()
   ]
   ```

### Exercise 6.1

Design a network for MNIST (28x28 grayscale images, 10 classes):

**Input**: 784 features (28 * 28 pixels)
**Output**: 10 classes (digits 0-9)

**Your design**:
```
Input (784)
  ↓
Linear(784 → 128)
  ↓
ReLU
  ↓
Linear(128 → 64)
  ↓
ReLU
  ↓
Linear(64 → 10)
  ↓
Softmax
```

**Parameters**: `(784*128 + 128) + (128*64 + 64) + (64*10 + 10) = 109,386`

---

## Lesson 7: Data Preprocessing

**Goal**: Learn essential data preparation techniques
**Time**: 20 minutes
**File**: `examples/pure_nn/data_utils_runtime.spl`

### Run the Example

```bash
bin/simple examples/pure_nn/data_utils_runtime.spl
```

### Expected Output

```
━━━ Example 2: Shuffle Dataset ━━━

After shuffling (seed=42):
  Sample 0: [5, 6] → y=0
  Sample 1: [9, 10] → y=0
  ...

━━━ Example 5: Feature Normalization ━━━

Normalized to [0, 1]:
  Sample 0: [0, 0]
  Sample 1: [0.2, 0.2]
  Sample 2: [0.4, 0.4]
```

### Key Concepts

1. **Shuffling prevents overfitting**:
   - Randomizes sample order each epoch
   - Prevents learning spurious patterns
   - Fisher-Yates algorithm: O(n), uniform

2. **Mini-batches speed up training**:
   - Full batch: All samples at once (slow for large datasets)
   - Mini-batch: Small batches (e.g., 32 samples)
   - Stochastic: 1 sample at a time (very noisy)

3. **Normalization helps convergence**:
   - Min-max: Scale to [0, 1]
   - Why: Prevents large feature values from dominating
   - Example: [1, 1000] → [0.0, 1.0]

4. **Train/test split**:
   - Training set: 70-80% (for learning)
   - Test set: 20-30% (for evaluation)
   - Never train on test data!

### Exercise 7.1

Implement a complete data pipeline:

```simple
# 1. Load data
val (X, y) = load_dataset()

# 2. Normalize features
val X_norm = normalize_features(X)

# 3. Split train/test
val split = train_test_split(X_norm, y, 0.8)
val train = split[0]
val test = split[1]

# 4. Training loop with shuffling
for epoch in 0..100:
    val shuffled = shuffle_data(train.X, train.y, epoch)
    val batches = create_batches(shuffled.X, shuffled.y, 32)

    for batch in batches:
        train_on_batch(model, batch)
```

---

## Next Steps

### Congratulations! 🎉

You've completed the Deep Learning Quickstart! You now know:

- ✅ Tensor operations and matrix math
- ✅ Neural network architecture
- ✅ Forward and backward propagation
- ✅ Gradient descent optimization
- ✅ Training loops and loss functions
- ✅ Data preprocessing pipeline

### Continue Learning

**1. Advanced Topics**:
- Momentum and Adam optimization
- Convolutional neural networks (CNNs)
- Recurrent neural networks (RNNs)
- Batch normalization and dropout

**2. Production Deployment**:
- Compile for performance: `bin/simple build --release`
- Use full `lib.pure.*` library (with generics)
- Multi-GPU training with CUDA
- Model checkpointing and loading

**3. Real-World Projects**:
- Image classification (MNIST, CIFAR-10)
- Natural language processing
- Time series prediction
- Reinforcement learning

### Resources

**Documentation**:
- Complete guide: `doc/guide/deep_learning_guide.md`
- Runtime examples: `examples/pure_nn/README_RUNTIME_COMPATIBLE.md`
- API reference: `src/lib/pure/` (for compiled mode)

**Examples**:
- MedGemma training: `examples/medgemma_korean/` (LLM fine-tuning)
- CUDA examples: `examples/cuda/` (Multi-GPU)
- PyTorch integration: `examples/torch/` (FFI)

**Community**:
- GitHub: `https://github.com/simple-lang/simple`
- Discussions: GitHub Discussions
- Issues: GitHub Issues

### Practice Projects

**Beginner**:
1. Train on different functions (y = x^2, y = sin(x))
2. Implement different activation functions (tanh, leaky ReLU)
3. Add learning rate scheduling

**Intermediate**:
1. Implement mini-batch SGD with momentum
2. Build a simple CNN for image classification
3. Create custom loss functions

**Advanced**:
1. Implement dropout regularization
2. Build an autoencoder
3. Fine-tune a pre-trained model (MedGemma)

---

## Troubleshooting

### Common Issues

**1. "function not found" errors**:
- **Cause**: Import path issues in interpreter mode
- **Fix**: Use runtime-compatible versions (`*_runtime.spl`)

**2. Slow training**:
- **Cause**: Large network or dataset in interpreter mode
- **Fix**: Reduce network size or use compiled mode

**3. NaN loss**:
- **Cause**: Learning rate too high
- **Fix**: Reduce learning rate (try 0.01 instead of 0.1)

**4. No convergence**:
- **Cause**: Learning rate too low or bad initialization
- **Fix**: Increase learning rate or reinitialize weights

### Getting Help

1. **Check examples**: All examples are verified working
2. **Read error messages**: They usually point to the issue
3. **Ask community**: GitHub Discussions
4. **File bug**: GitHub Issues (with minimal reproduction)

---

**Tutorial Complete! Happy Learning! 🚀**

*Last updated: 2026-02-16*
*Simple Language Version: 0.4.0*
