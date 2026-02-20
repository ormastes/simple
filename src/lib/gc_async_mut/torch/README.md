# PyTorch Simple API

This library provides a comprehensive PyTorch-like API for neural network development in Simple. It wraps the low-level FFI bindings with a high-level, idiomatic Simple interface designed to feel familiar to PyTorch users.

## Architecture

The library follows a layered architecture:

1. **Native (C++)**: PyTorch C++ (libtorch) bindings in `.build/rust/ffi_torch/simple-torch/`
2. **SFFI**: Rust FFI layer in `.build/rust/ffi_torch/src/lib.rs` and Simple bindings in `ffi.spl`
3. **Simple API**: High-level PyTorch-like API in `mod.spl` (this library)

## Features

### Core Tensor Operations

The `Tensor` class provides:

- **Creation**: `zeros()`, `ones()`, `randn()`
- **Properties**: `shape()`, `ndim()`, `numel()`, `size(dim)`
- **Arithmetic**: `add()`, `sub()`, `mul()`, `div()`, `matmul()`, `mm()`, `dot()`
- **Activations**: `relu()`, `sigmoid()`, `tanh()`, `softmax()` (stub), `log_softmax()` (stub)
- **Device Management**: `cuda()`, `cpu()`, `is_cuda()`, `to_device()`
- **Memory**: Automatic RAII cleanup via `drop()`, manual `clone()`
- **Autograd**: `backward()` (stub), `zero_grad()` (stub), `requires_grad()` (stub), `detach()` (stub)
- **Reshaping**: `view()` (stub), `reshape()` (stub), `transpose()` (stub), `permute()` (stub), `squeeze()` (stub), `unsqueeze()` (stub)

### Neural Network Layers

- **Linear**: Fully connected layer with weight and bias
- **Conv2d**: 2D convolutional layer (forward pass stub)
- **MaxPool2d**: 2D max pooling layer (stub)
- **BatchNorm2d**: Batch normalization layer (stub)
- **Dropout**: Dropout regularization with train/eval mode (stub)

### Loss Functions

- **MSELoss**: Mean Squared Error loss
- **CrossEntropyLoss**: Cross-entropy loss for classification (stub)

### Optimizers

All optimizers support `step()` and `zero_grad()`:

- **SGD**: Stochastic Gradient Descent with momentum
- **Adam**: Adaptive Moment Estimation with beta parameters
- **RMSprop**: Root Mean Square Propagation

### Model Containers

- **Sequential**: Chain layers together with automatic forward pass
- **Stream**: CUDA stream for asynchronous GPU operations

### Utility Functions

- `torch_available()`: Check if PyTorch backend is loaded
- `torch_version()`: Get PyTorch version string
- `cuda_available()`: Check if CUDA is available
- `no_grad()`: Context manager for disabling gradients (stub)
- `set_seed()` / `manual_seed()`: Set random seed (stub)

## Usage Examples

### Basic Tensor Operations

```simple
use lib.torch.mod.{Tensor}

val t1 = Tensor.zeros([3, 3])
val t2 = Tensor.ones([3, 3])
val t3 = t1.add(t2)  # Element-wise addition
val t4 = Tensor.randn([3, 3])  # Random normal

print t3.shape()  # [3, 3]
print t3.numel()  # 9
```

### Linear Layer

```simple
use lib.torch.mod.{Linear, Tensor}

val layer = Linear.create(784, 128)  # 784 inputs -> 128 outputs
val x = Tensor.randn([32, 784])      # Batch of 32
val y = layer.forward(x)
print y.shape()  # [32, 128]
```

### Multi-Layer Perceptron

```simple
use lib.torch.mod.{Sequential, Linear, Tensor}

val model = Sequential.create()
model.add_layer_linear(Linear.create(784, 256))
model.add_layer_linear(Linear.create(256, 128))
model.add_layer_linear(Linear.create(128, 10))

val x = Tensor.randn([32, 784])
val output = model.forward(x)
print output.shape()  # [32, 10]
```

### Training Loop Structure

```simple
use lib.torch.mod.{Sequential, Linear, SGD, MSELoss, Tensor}

val model = Sequential.create()
model.add_layer_linear(Linear.create(10, 20))
model.add_layer_linear(Linear.create(20, 2))

val optimizer = SGD.create(model.parameters(), 0, 0)  # lr=0.01, momentum=0.9
val criterion = MSELoss.create()

# Training iteration (requires autograd FFI for backward):
val input_data = Tensor.randn([32, 10])
val target = Tensor.randn([32, 2])

optimizer.zero_grad()
val output = model.forward(input_data)
val loss = criterion.forward(output, target)
# loss.backward()  # Not yet implemented - requires autograd FFI
optimizer.step()
```

### Convolutional Neural Network

```simple
use lib.torch.mod.{Conv2d, MaxPool2d, Linear, Sequential, Tensor}

val conv1 = Conv2d.create(3, 64, 3, 1, 1)  # 3 -> 64 channels, 3x3 kernel
val pool = MaxPool2d.create(2, 2)          # 2x2 pooling

val images = Tensor.randn([8, 3, 224, 224])  # Batch of 8 RGB images
val features = conv1.forward(images)
val pooled = pool.forward(features)
print pooled.shape()  # [8, 64, 112, 112]
```

### CUDA Operations

```simple
use lib.torch.mod.{Tensor, cuda_available}

val t = Tensor.randn([100, 100])

if cuda_available():
    val t_gpu = t.cuda(0)       # Move to GPU device 0
    val result = t_gpu.add(t_gpu)
    val t_cpu = result.cpu()    # Move back to CPU
    print t_cpu.shape()
```

### Optimizer Comparison

```simple
use lib.torch.mod.{SGD, Adam, RMSprop, Tensor}

val params = [Tensor.randn([10, 5]), Tensor.randn([5])]

val sgd = SGD.create(params, 0, 0)           # Learning rate 0.01, momentum 0.9
val adam = Adam.create(params, 0, 0, 0)      # Learning rate 0.001, beta1=0.9, beta2=0.999
val rmsprop = RMSprop.create(params, 0, 0, 0) # Learning rate 0.01, alpha=0.99, eps=1e-8

# All optimizers support:
sgd.step()
sgd.zero_grad()
```

## API Reference

### Tensor

#### Static Methods

- `zeros(dims: [i64]) -> Tensor` - Create tensor filled with zeros
- `ones(dims: [i64]) -> Tensor` - Create tensor filled with ones
- `randn(dims: [i64]) -> Tensor` - Create tensor with random normal values
- `from_handle(handle: i64) -> Tensor` - Internal: wrap FFI handle

#### Instance Methods

**Properties:**
- `ndim() -> i64` - Number of dimensions
- `numel() -> i64` - Total number of elements
- `shape() -> [i64]` - Shape as array
- `size(dim: i64) -> i64` - Size of specific dimension

**Arithmetic:**
- `add(other: Tensor) -> Tensor` - Element-wise addition
- `sub(other: Tensor) -> Tensor` - Element-wise subtraction
- `mul(other: Tensor) -> Tensor` - Element-wise multiplication
- `div(other: Tensor) -> Tensor` - Element-wise division
- `matmul(other: Tensor) -> Tensor` - Matrix multiplication
- `mm(other: Tensor) -> Tensor` - Alias for matmul
- `dot(other: Tensor) -> Tensor` - Dot product

**Activations:**
- `relu() -> Tensor` - ReLU activation
- `sigmoid() -> Tensor` - Sigmoid activation
- `tanh() -> Tensor` - Tanh activation
- `softmax(dim: i64) -> Tensor` - Softmax (stub)
- `log_softmax(dim: i64) -> Tensor` - Log-softmax (stub)

**Device:**
- `cuda(device_id: i64) -> Tensor` - Move to CUDA device
- `cpu() -> Tensor` - Move to CPU
- `is_cuda() -> bool` - Check if on CUDA
- `to_device(device: text) -> Tensor` - Move to named device

**Autograd (stubs):**
- `backward()` - Compute gradients
- `zero_grad()` - Zero out gradients
- `requires_grad(value: bool) -> Tensor` - Set gradient flag
- `detach() -> Tensor` - Detach from graph

**Memory:**
- `drop()` - Free memory (automatic)
- `clone() -> Tensor` - Deep copy

### Layers

#### Linear

- `Linear.create(in_features: i64, out_features: i64) -> Linear`
- `Linear.create_with_bias(in_features: i64, out_features: i64, use_bias: bool) -> Linear`
- `forward(x: Tensor) -> Tensor`
- `parameters() -> [Tensor]`

#### Conv2d

- `Conv2d.create(in_channels: i64, out_channels: i64, kernel_size: i64, stride: i64, padding: i64) -> Conv2d`
- `forward(x: Tensor) -> Tensor` (stub)
- `parameters() -> [Tensor]`

#### MaxPool2d

- `MaxPool2d.create(kernel_size: i64, stride: i64) -> MaxPool2d`
- `forward(x: Tensor) -> Tensor` (stub)

#### BatchNorm2d

- `BatchNorm2d.create(num_features: i64) -> BatchNorm2d`
- `forward(x: Tensor) -> Tensor` (stub)
- `parameters() -> [Tensor]`

#### Dropout

- `Dropout.create(p: i64) -> Dropout`
- `forward(x: Tensor) -> Tensor` (stub)
- `train()` - Set training mode
- `eval()` - Set evaluation mode

### Loss Functions

#### MSELoss

- `MSELoss.create() -> MSELoss`
- `forward(pred: Tensor, target: Tensor) -> Tensor`

#### CrossEntropyLoss

- `CrossEntropyLoss.create() -> CrossEntropyLoss`
- `forward(logits: Tensor, targets: Tensor) -> Tensor` (stub)

### Optimizers

All optimizers have:
- `create(parameters: [Tensor], ...) -> Optimizer`
- `step()` - Update parameters (requires autograd)
- `zero_grad()` - Zero out gradients

#### SGD

- `SGD.create(parameters: [Tensor], lr: i64, momentum: i64) -> SGD`

#### Adam

- `Adam.create(parameters: [Tensor], lr: i64, beta1: i64, beta2: i64) -> Adam`

#### RMSprop

- `RMSprop.create(parameters: [Tensor], lr: i64, alpha: i64, eps: i64) -> RMSprop`

### Sequential

- `Sequential.create() -> Sequential`
- `add_layer_linear(layer: Linear)` - Add Linear layer
- `add_layer_conv2d(layer: Conv2d)` - Add Conv2d layer
- `forward(x: Tensor) -> Tensor` - Forward pass through all layers
- `parameters() -> [Tensor]` - Get all parameters

### Stream

- `Stream.create(device_id: i64) -> Stream`
- `sync()` - Wait for all operations
- `query() -> bool` - Check completion
- `drop()` - Free stream (automatic)

## Implementation Status

### Fully Implemented ✅

- Tensor creation (zeros, ones, randn)
- Tensor properties (shape, ndim, numel)
- Basic arithmetic (add, mul, matmul)
- Derived arithmetic (sub via add, div via mul)
- Core activations (relu, sigmoid, tanh)
- Device operations (cuda, cpu, is_cuda)
- Memory management (RAII with drop)
- Linear layer with bias
- Sequential container
- MSE loss
- All optimizer structures (SGD, Adam, RMSprop)
- Stream operations (create, sync, query)

### Partially Implemented ⚠️

- Autograd (stubs - requires FFI extension)
- Reshaping operations (stubs - requires FFI extension)
- Conv2d forward pass (stub - requires FFI extension)
- MaxPool2d (stub - requires FFI extension)
- BatchNorm2d (stub - requires FFI extension)
- Dropout (stub - requires FFI extension)
- CrossEntropyLoss (stub - requires FFI extension)
- Optimizer step() (stub - requires autograd FFI)
- Softmax/LogSoftmax (stubs - requires FFI extension)

### Not Yet Implemented ❌

- Gradient computation and backpropagation
- Advanced reshaping (view, transpose, permute, squeeze, unsqueeze)
- Convolution forward pass
- Pooling operations
- Batch normalization computation
- Dropout masking
- Cross-entropy computation
- Parameter updates in optimizers
- Random seed setting

## Future Extensions

To make this a production-ready PyTorch alternative, the following FFI extensions are needed:

1. **Autograd System**:
   - `backward()` implementation
   - Gradient storage and computation
   - Computation graph tracking

2. **Tensor Operations**:
   - View/reshape operations
   - Transpose and permute
   - Squeeze/unsqueeze
   - Indexing and slicing

3. **Convolution Operations**:
   - Forward pass for Conv2d
   - Backward pass (autograd)
   - Different padding modes
   - Dilated convolutions

4. **Pooling Operations**:
   - MaxPool2d forward/backward
   - AvgPool2d
   - Adaptive pooling

5. **Normalization**:
   - BatchNorm2d forward/backward
   - LayerNorm
   - InstanceNorm

6. **Loss Functions**:
   - CrossEntropyLoss
   - NLLLoss
   - BCELoss
   - Custom loss functions

7. **Optimizers**:
   - Parameter update logic
   - Learning rate schedulers
   - Gradient clipping

8. **Advanced Features**:
   - Mixed precision training
   - Distributed training
   - Model saving/loading
   - JIT compilation

## Example Program

See `examples/torch_example.spl` for a comprehensive demonstration of all features.

## Building

The PyTorch FFI requires:
- PyTorch C++ (libtorch) installed
- Rust toolchain for FFI layer
- C++ compiler for bridge code

Build the library:
```bash
cd .build/rust/ffi_torch
cargo build --release
```

## Testing

Run the example:
```bash
bin/simple run examples/torch_example.spl
```

## License

Same as the Simple compiler project.
