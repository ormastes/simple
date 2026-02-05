# Pure Simple DL API Reference

Complete API documentation for Pure Simple Deep Learning library.

## Table of Contents

1. [Core Tensor API](#core-tensor-api)
2. [Tensor Operations](#tensor-operations)
3. [Neural Network Layers](#neural-network-layers)
4. [Training Utilities](#training-utilities)
5. [Acceleration Layer](#acceleration-layer)
6. [PyTorch FFI](#pytorch-ffi)
7. [Data Utilities](#data-utilities)

---

## Core Tensor API

### Module: `lib.pure.tensor`

Core tensor implementation with flat array storage.

#### PureTensor<T>

```simple
class PureTensor<T>:
    data: [T]           # Flat array storage
    shape: [i64]        # Dimensions [batch, height, width, ...]
    strides: [i64]      # Memory layout strides
```

**Factory Methods:**

```simple
static fn zeros(shape: [i64]) -> PureTensor<f64>
```
Create tensor filled with zeros.

**Parameters:**
- `shape`: Dimensions `[batch, rows, cols, ...]`

**Returns:** Tensor with all elements = 0.0

**Example:**
```simple
val t = PureTensor.zeros([2, 3])  # 2×3 matrix of zeros
```

---

```simple
static fn ones(shape: [i64]) -> PureTensor<f64>
```
Create tensor filled with ones.

**Parameters:**
- `shape`: Dimensions

**Returns:** Tensor with all elements = 1.0

**Example:**
```simple
val t = PureTensor.ones([3, 3])  # 3×3 identity-ready matrix
```

---

```simple
static fn from_data(data: [T], shape: [i64]) -> PureTensor<T>
```
Create tensor from existing data array.

**Parameters:**
- `data`: Flat array of elements (length must match product of shape)
- `shape`: Dimensions

**Returns:** Tensor wrapping the data

**Example:**
```simple
val t = PureTensor.from_data([1.0, 2.0, 3.0, 4.0], [2, 2])
# [[1.0, 2.0],
#  [3.0, 4.0]]
```

---

```simple
static fn randn(shape: [i64]) -> PureTensor<f64>
```
Create tensor with random normal distribution N(0, 1).

**Parameters:**
- `shape`: Dimensions

**Returns:** Tensor with random values (mean=0, std=1)

**Example:**
```simple
val weights = PureTensor.randn([256, 784])  # Random weight init
```

**Instance Methods:**

```simple
fn get(indices: [i64]) -> T
```
Get element at multi-dimensional index.

**Parameters:**
- `indices`: Index for each dimension `[batch_idx, row_idx, col_idx, ...]`

**Returns:** Element at that position

**Example:**
```simple
val t = PureTensor.from_data([1, 2, 3, 4], [2, 2])
val x = t.get([0, 1])  # 2 (first row, second column)
```

---

```simple
me set(indices: [i64], value: T)
```
Set element at multi-dimensional index.

**Parameters:**
- `indices`: Index for each dimension
- `value`: New value

**Example:**
```simple
var t = PureTensor.zeros([2, 2])
t.set([1, 1], 5.0)  # Bottom-right = 5.0
```

---

```simple
fn numel() -> i64
```
Total number of elements (product of shape dimensions).

**Returns:** Total element count

**Example:**
```simple
val t = PureTensor.zeros([2, 3, 4])
val count = t.numel()  # 24 (2 * 3 * 4)
```

---

```simple
fn reshape(new_shape: [i64]) -> PureTensor<T>
```
Create view with different shape (must have same numel).

**Parameters:**
- `new_shape`: New dimensions

**Returns:** Reshaped tensor (shares data)

**Example:**
```simple
val t = PureTensor.randn([6])
val matrix = t.reshape([2, 3])  # Convert vector to 2×3 matrix
```

---

## Tensor Operations

### Module: `lib.pure.tensor_ops`

Pure Simple implementations of tensor operations.

#### Element-wise Operations

```simple
fn add(a: PureTensor<f64>, b: PureTensor<f64>) -> PureTensor<f64>
```
Element-wise addition: `result[i] = a[i] + b[i]`

**Broadcasting:** Supported (smaller tensor broadcast to larger)

**Example:**
```simple
val a = PureTensor.ones([2, 3])
val b = PureTensor.ones([2, 3])
val c = add(a, b)  # All elements = 2.0
```

---

```simple
fn sub(a: PureTensor<f64>, b: PureTensor<f64>) -> PureTensor<f64>
fn mul(a: PureTensor<f64>, b: PureTensor<f64>) -> PureTensor<f64>
fn div(a: PureTensor<f64>, b: PureTensor<f64>) -> PureTensor<f64>
```
Element-wise subtraction, multiplication, division.

---

```simple
fn neg(x: PureTensor<f64>) -> PureTensor<f64>
```
Negate all elements: `result[i] = -x[i]`

---

#### Matrix Operations

```simple
fn matmul(a: PureTensor<f64>, b: PureTensor<f64>) -> PureTensor<f64>
```
Matrix multiplication: `C = A @ B`

**Requirements:**
- `a.shape = [M, K]`
- `b.shape = [K, N]`
- Result shape = `[M, N]`

**Algorithm:** Naive O(n³) triple loop (pure Simple)

**Performance:**
- 100×100: ~40ms
- 500×500: ~5sec
- 1000×1000: ~40sec

**Example:**
```simple
val A = PureTensor.randn([10, 20])  # 10×20 matrix
val B = PureTensor.randn([20, 5])   # 20×5 matrix
val C = matmul(A, B)                # 10×5 result
```

---

```simple
fn transpose(x: PureTensor<f64>) -> PureTensor<f64>
```
Transpose 2D matrix (swap rows ↔ columns).

**Requirements:** 2D tensor only

**Example:**
```simple
val A = PureTensor.from_data([1, 2, 3, 4], [2, 2])
# [[1, 2],
#  [3, 4]]

val AT = transpose(A)
# [[1, 3],
#  [2, 4]]
```

---

#### Reduction Operations

```simple
fn sum(x: PureTensor<f64>) -> f64
```
Sum all elements.

**Example:**
```simple
val t = PureTensor.from_data([1, 2, 3, 4], [2, 2])
val total = sum(t)  # 10.0
```

---

```simple
fn mean(x: PureTensor<f64>) -> f64
fn max(x: PureTensor<f64>) -> f64
fn min(x: PureTensor<f64>) -> f64
```
Mean, maximum, minimum of all elements.

---

#### Activation Functions

```simple
fn relu(x: PureTensor<f64>) -> PureTensor<f64>
```
Rectified Linear Unit: `max(0, x)`

**Example:**
```simple
val x = PureTensor.from_data([-1, 0, 1, 2], [2, 2])
val activated = relu(x)  # [0, 0, 1, 2]
```

---

```simple
fn sigmoid(x: PureTensor<f64>) -> PureTensor<f64>
```
Sigmoid activation: `1 / (1 + exp(-x))`

**Range:** (0, 1)

**Example:**
```simple
val logits = PureTensor.randn([10, 1])
val probs = sigmoid(logits)  # Probabilities in (0, 1)
```

---

```simple
fn tanh(x: PureTensor<f64>) -> PureTensor<f64>
```
Hyperbolic tangent: `tanh(x)`

**Range:** (-1, 1)

---

```simple
fn softmax(x: PureTensor<f64>, dim: i64) -> PureTensor<f64>
```
Softmax activation along dimension.

**Formula:** `exp(x_i) / sum(exp(x_j))`

**Use case:** Multi-class classification

**Example:**
```simple
val logits = PureTensor.randn([10, 3])  # 10 samples, 3 classes
val probs = softmax(logits, dim: 1)    # Probabilities per class
# Each row sums to 1.0
```

---

## Neural Network Layers

### Module: `lib.pure.nn`

Neural network building blocks.

#### Linear Layer

```simple
class Linear:
    weights: PureTensor<f64>    # [out_features, in_features]
    bias: PureTensor<f64>?      # [out_features] (optional)
    in_features: i64
    out_features: i64
```

**Constructor:**
```simple
static fn create(in_features: i64, out_features: i64, bias: bool = true) -> Linear
```

Creates fully-connected layer with Xavier initialization.

**Parameters:**
- `in_features`: Input dimension
- `out_features`: Output dimension
- `bias`: Include bias term (default: true)

**Example:**
```simple
val fc1 = Linear.create(784, 256)  # MNIST hidden layer
val fc2 = Linear.create(256, 10)   # Output layer (10 classes)
```

**Forward Pass:**
```simple
fn forward(x: PureTensor<f64>) -> PureTensor<f64>
```

Computes: `y = xW^T + b`

**Parameters:**
- `x`: Input tensor `[batch_size, in_features]`

**Returns:** Output tensor `[batch_size, out_features]`

**Example:**
```simple
val layer = Linear.create(784, 256)
val x = PureTensor.randn([32, 784])  # Batch of 32 samples
val y = layer.forward(x)              # [32, 256] output
```

---

#### Activation Layers

```simple
class ReLU:
    fn forward(x: PureTensor<f64>) -> PureTensor<f64>
```

Applies ReLU activation element-wise.

**Example:**
```simple
val relu = ReLU()
val x = PureTensor.from_data([-1, 0, 1, 2], [2, 2])
val y = relu.forward(x)  # [0, 0, 1, 2]
```

---

```simple
class Sigmoid:
    fn forward(x: PureTensor<f64>) -> PureTensor<f64>

class Tanh:
    fn forward(x: PureTensor<f64>) -> PureTensor<f64>
```

Sigmoid and tanh activation layers.

---

#### Sequential Container

```simple
class Sequential:
    layers: [Layer]

    fn forward(x: PureTensor<f64>) -> PureTensor<f64>
    fn parameters() -> [PureTensor<f64>]
```

Chains multiple layers sequentially.

**Example:**
```simple
val model = Sequential(layers: [
    Linear.create(784, 256),
    ReLU(),
    Linear.create(256, 128),
    ReLU(),
    Linear.create(128, 10)
])

val x = PureTensor.randn([32, 784])
val output = model.forward(x)  # [32, 10] logits
```

---

## Training Utilities

### Module: `lib.pure.training`

Loss functions and training infrastructure.

#### Loss Functions

```simple
fn mse_loss(predictions: PureTensor<f64>, targets: PureTensor<f64>) -> f64
```

Mean Squared Error loss: `mean((predictions - targets)^2)`

**Use case:** Regression problems

**Example:**
```simple
val pred = model.forward(x)
val loss = mse_loss(pred, y_true)
print "Loss: {loss}"
```

---

```simple
fn mae_loss(predictions: PureTensor<f64>, targets: PureTensor<f64>) -> f64
```

Mean Absolute Error loss: `mean(abs(predictions - targets))`

---

#### LinearModel

```simple
class LinearModel:
    weights: PureTensor<f64>
    bias: f64

    fn predict(x: PureTensor<f64>) -> PureTensor<f64>
    fn fit(X: PureTensor<f64>, y: PureTensor<f64>, lr: f64 = 0.01, epochs: i64 = 100)
```

Simple linear regression model with gradient descent.

**Example:**
```simple
val model = LinearModel.create(n_features: 5)
model.fit(X_train, y_train, lr: 0.01, epochs: 100)
val predictions = model.predict(X_test)
```

---

## Acceleration Layer

### Module: `lib.pure.accel`

Configures Pure Simple vs FFI acceleration.

#### Acceleration Modes

```simple
enum AccelMode:
    PureSimple      # Never use FFI (pure Simple only)
    PyTorchFFI      # Always use FFI if available
    Auto            # Smart threshold-based selection
```

#### Configuration Functions

```simple
fn set_acceleration(mode: AccelMode)
```

Set global acceleration mode.

**Example:**
```simple
use lib.pure.accel (set_acceleration, AccelMode)

set_acceleration(AccelMode.Auto)  # Smart selection (recommended)
```

---

```simple
fn get_current_mode() -> AccelMode
```

Get current acceleration mode.

---

```simple
fn set_threshold(operation: text, threshold: i64)
```

Set element count threshold for FFI usage in Auto mode.

**Parameters:**
- `operation`: Operation name ("matmul", "elementwise", "activations")
- `threshold`: Minimum element count to use FFI

**Example:**
```simple
# Use FFI for matmul with >500k elements
set_threshold("matmul", 500_000)

# Use FFI for element-wise ops with >5M elements
set_threshold("elementwise", 5_000_000)
```

**Default Thresholds:**
- `matmul`: 1,000,000
- `elementwise`: 10,000,000
- `activations`: never (∞)

---

```simple
fn get_threshold(operation: text) -> i64
```

Get current threshold for an operation.

---

#### Decision Logic

```simple
fn should_use_ffi(operation: text, numel: i64) -> bool
```

Decides whether to use FFI for a given operation.

**Logic:**
1. If mode = PureSimple: return false
2. If mode = PyTorchFFI: return ffi_available
3. If mode = Auto:
   - If FFI not available: return false
   - If numel > threshold: return true
   - Else: return false

**Example:**
```simple
val a = PureTensor.randn([1000, 1000])  # 1M elements
val b = PureTensor.randn([1000, 1000])

# In Auto mode with default threshold (1M):
val use_ffi = should_use_ffi("matmul", a.numel() * b.numel())
# true (1M * 1M = 1T > 1M threshold)
```

---

#### Statistics

```simple
class AccelStats:
    pure_count: i64        # Number of Pure Simple operations
    ffi_count: i64         # Number of FFI operations
    fallback_count: i64    # FFI failures that fell back to Pure Simple

fn get_stats() -> AccelStats
```

Get acceleration statistics.

**Example:**
```simple
val stats = get_stats()
print "Pure: {stats.pure_count}, FFI: {stats.ffi_count}, Fallbacks: {stats.fallback_count}"
```

---

```simple
fn reset_stats()
```

Reset statistics counters to zero.

---

## PyTorch FFI

### Module: `lib.pure.torch_ffi`

PyTorch FFI wrapper functions (two-tier pattern).

#### Availability Check

```simple
fn torch_available() -> bool
```

Check if PyTorch FFI library is loaded.

**Returns:** true if FFI available, false otherwise

**Example:**
```simple
if torch_available():
    print "✅ PyTorch FFI enabled"
    set_acceleration(AccelMode.Auto)
else:
    print "ℹ️  Pure Simple only"
    set_acceleration(AccelMode.PureSimple)
```

---

```simple
fn torch_version() -> text
fn torch_cuda_available() -> bool
```

Get PyTorch version string and CUDA availability.

---

#### Conversion Functions

```simple
fn pure_to_torch(tensor: PureTensor<f64>) -> i64
```

Convert PureTensor to PyTorch handle.

**Returns:** Opaque handle (integer) for PyTorch tensor

**Note:** Must call `rt_torch_free()` to avoid memory leak!

---

```simple
fn torch_to_pure(handle: i64) -> PureTensor<f64>
```

Convert PyTorch tensor handle back to PureTensor.

**Parameters:**
- `handle`: PyTorch tensor handle from previous conversion

**Returns:** PureTensor with copied data

---

#### FFI Operation Wrappers

```simple
fn matmul_torch_ffi(a: PureTensor<f64>, b: PureTensor<f64>) -> PureTensor<f64>
```

Matrix multiplication via PyTorch FFI.

**Automatically manages memory** (frees all handles).

**Example:**
```simple
val a = PureTensor.randn([1000, 1000])
val b = PureTensor.randn([1000, 1000])
val c = matmul_torch_ffi(a, b)  # ~50ms (vs ~40sec in pure Simple)
```

---

```simple
fn add_torch_ffi(a: PureTensor<f64>, b: PureTensor<f64>) -> PureTensor<f64>
fn mul_torch_ffi(a: PureTensor<f64>, b: PureTensor<f64>) -> PureTensor<f64>
fn relu_torch_ffi(x: PureTensor<f64>) -> PureTensor<f64>
```

Element-wise operations via FFI (with automatic memory management).

---

#### Raw FFI Functions (Advanced)

**⚠️ Warning:** These functions require manual memory management!

```simple
extern fn rt_torch_zeros(shape: [i64], dtype: text, device: text) -> i64
extern fn rt_torch_from_data(data: [f64], shape: [i64]) -> i64
extern fn rt_torch_matmul(a: i64, b: i64) -> i64
extern fn rt_torch_free(handle: i64)
```

**Use high-level wrappers instead** to avoid memory leaks.

---

## Data Utilities

### Module: `lib.pure.data`

Data preprocessing utilities.

#### Normalization

```simple
fn normalize(data: PureTensor<f64>, min_val: f64, max_val: f64) -> PureTensor<f64>
```

Normalize data to [0, 1] range.

**Formula:** `(x - min) / (max - min)`

**Example:**
```simple
val pixels = PureTensor.from_data([0, 127, 255], [3])
val normalized = normalize(pixels, min_val: 0.0, max_val: 255.0)
# [0.0, 0.498, 1.0]
```

---

```simple
fn standardize(data: PureTensor<f64>) -> PureTensor<f64>
```

Standardize data to mean=0, std=1.

**Formula:** `(x - mean) / std`

**Example:**
```simple
val features = PureTensor.randn([100, 10])
val standardized = standardize(features)
val new_mean = mean(standardized)  # ~0.0
```

---

## Complete Example

```simple
use lib.pure.tensor (PureTensor)
use lib.pure.tensor_ops (matmul, add, relu)
use lib.pure.nn (Linear, ReLU, Sequential)
use lib.pure.training (mse_loss, LinearModel)
use lib.pure.accel (set_acceleration, AccelMode, get_stats)
use lib.pure.torch_ffi (torch_available)
use lib.pure.data (normalize)

# Configure acceleration
if torch_available():
    set_acceleration(AccelMode.Auto)

# Prepare data
val X_raw = PureTensor.randn([100, 20])  # 100 samples, 20 features
val X = normalize(X_raw, min_val: -3.0, max_val: 3.0)
val y = PureTensor.randn([100, 1])

# Build model
val model = Sequential(layers: [
    Linear.create(20, 64),
    ReLU(),
    Linear.create(64, 32),
    ReLU(),
    Linear.create(32, 1)
])

# Training loop (simplified)
var epoch = 0
while epoch < 10:
    val predictions = model.forward(X)
    val loss = mse_loss(predictions, y)
    print "Epoch {epoch}: loss = {loss}"
    epoch = epoch + 1

# Report stats
val stats = get_stats()
print "Acceleration: {stats.ffi_count} FFI, {stats.pure_count} Pure"
```

---

## Module Import Summary

```simple
# Core tensors
use lib.pure.tensor (PureTensor)
use lib.pure.tensor_ops (add, mul, matmul, relu, sigmoid, softmax)

# Neural networks
use lib.pure.nn (Linear, ReLU, Sigmoid, Tanh, Sequential)

# Training
use lib.pure.training (mse_loss, mae_loss, LinearModel)

# Acceleration
use lib.pure.accel (set_acceleration, AccelMode, get_stats, reset_stats)
use lib.pure.torch_ffi (torch_available, matmul_torch_ffi)

# Data utilities
use lib.pure.data (normalize, standardize)
```

---

## See Also

- **User Guide:** `doc/guide/acceleration_user_guide.md`
- **Examples:** `examples/pure_nn/`
- **Tests:** `src/lib/pure/test/`
- **Design:** `doc/design/pure_dl_sffi_acceleration_plan.md`
