# PyTorch Integration Research

**Date:** 2025-12-26
**Status:** Research Complete
**Target:** PyTorch 2.5+ (LibTorch C++ API + Python interop)

## Executive Summary

This document outlines research for integrating Simple language with PyTorch for machine learning and deep learning applications. The goal is to provide a type-safe, high-performance ML framework that leverages both LibTorch's C++ API and Python interop when needed.

**Key Findings:**
- LibTorch C++ API provides complete PyTorch functionality without Python
- DLPack enables zero-copy tensor sharing
- Python bridge needed for ecosystem (datasets, pretrained models)
- Simple's type system can provide better safety than Python PyTorch

---

## 1. PyTorch Architecture Overview

### 1.1 Core Components

**LibTorch (C++ API):**
- Complete PyTorch functionality in C++
- Same backend as Python PyTorch
- ATen tensor library
- Autograd engine
- JIT compiler (TorchScript)

**ATen (A Tensor Library):**
- Core tensor operations
- CPU and CUDA backends
- Automatic differentiation
- Broadcasting and shape inference

**Autograd:**
- Automatic differentiation engine
- Builds dynamic computation graph
- Backward pass for gradients

**C10:**
- Core tensor type definitions
- Dispatcher (operator dispatch)
- Device abstraction (CPU/CUDA/etc.)

### 1.2 Tensor System

**Core Tensor Type:**
```cpp
// LibTorch C++ API
#include <torch/torch.h>

// Create tensors
auto tensor = torch::randn({3, 4});              // CPU
auto gpu_tensor = torch::randn({3, 4}, torch::kCUDA);  // GPU

// Operations
auto result = tensor.matmul(other);
auto mean = tensor.mean();
auto gradient = tensor.grad();
```

**Tensor Properties:**
- Data pointer (CPU or GPU memory)
- Shape (dimensions)
- Strides (memory layout)
- Dtype (float32, int64, etc.)
- Device (cpu, cuda:0, cuda:1, etc.)
- Requires_grad (for autograd)

**Memory Layout:**
```cpp
// Contiguous vs. strided
auto t = torch::randn({10, 20});
auto t_transposed = t.transpose(0, 1);  // Not contiguous

// Make contiguous
auto t_contig = t_transposed.contiguous();
```

### 1.3 Autograd System

**Computation Graph:**
```cpp
// Create tensors with requires_grad
auto x = torch::ones({2, 2}, torch::requires_grad());
auto y = x + 2;
auto z = y * y * 3;
auto out = z.mean();

// Backward pass
out.backward();

// Access gradients
std::cout << x.grad() << std::endl;
```

**Gradient Flow:**
- Forward pass builds computation graph
- Each operation creates a `Function` node
- Backward pass traverses graph in reverse
- Chain rule applied automatically

### 1.4 Neural Network Modules

**nn::Module:**
```cpp
#include <torch/torch.h>

// Define model
struct Net : torch::nn::Module {
    Net() {
        fc1 = register_module("fc1", torch::nn::Linear(784, 128));
        fc2 = register_module("fc2", torch::nn::Linear(128, 10));
    }

    torch::Tensor forward(torch::Tensor x) {
        x = torch::relu(fc1->forward(x));
        x = fc2->forward(x);
        return torch::log_softmax(x, 1);
    }

    torch::nn::Linear fc1{nullptr}, fc2{nullptr};
};

// Use model
Net model;
auto output = model.forward(input);
```

**Built-in Modules:**
- Linear, Conv2d, Conv3d
- RNN, LSTM, GRU
- BatchNorm, LayerNorm
- Dropout, Embedding
- Transformer layers

### 1.5 Optimizers

**Optimization Algorithms:**
```cpp
// SGD
auto sgd = torch::optim::SGD(
    model->parameters(),
    torch::optim::SGDOptions(0.01).momentum(0.9)
);

// Adam
auto adam = torch::optim::Adam(
    model->parameters(),
    torch::optim::AdamOptions(0.001)
);

// Training step
optimizer.zero_grad();
auto output = model->forward(input);
auto loss = torch::mse_loss(output, target);
loss.backward();
optimizer.step();
```

### 1.6 JIT Compilation (TorchScript)

**TorchScript:**
- Ahead-of-time compilation
- Export models from Python → C++
- Optimize for inference
- Mobile deployment

```cpp
// Load TorchScript model
torch::jit::script::Module module;
module = torch::jit::load("model.pt");

// Inference
std::vector<torch::jit::IValue> inputs;
inputs.push_back(torch::ones({1, 3, 224, 224}));
auto output = module.forward(inputs).toTensor();
```

---

## 2. LibTorch C++ API

### 2.1 Tensor Creation

**Factory Functions:**
```cpp
// Zeros, ones, full
auto zeros = torch::zeros({3, 4});
auto ones = torch::ones({3, 4});
auto full = torch::full({3, 4}, 3.14);

// Random
auto randn = torch::randn({3, 4});  // Normal distribution
auto rand = torch::rand({3, 4});    // Uniform [0, 1)

// From data
std::vector<float> data = {1, 2, 3, 4};
auto from_blob = torch::from_blob(data.data(), {2, 2});

// Arange, linspace
auto arange = torch::arange(0, 10, 1);
auto linspace = torch::linspace(0, 1, 100);
```

### 2.2 Tensor Operations

**Element-wise:**
```cpp
auto a = torch::randn({3, 4});
auto b = torch::randn({3, 4});

auto sum = a + b;
auto prod = a * b;
auto sqrt = a.sqrt();
auto exp = a.exp();
auto log = a.log();
auto relu = torch::relu(a);
```

**Reductions:**
```cpp
auto sum = tensor.sum();
auto mean = tensor.mean();
auto max = tensor.max();
auto argmax = tensor.argmax();

// Along dimension
auto row_sums = tensor.sum(/*dim=*/1);
```

**Linear Algebra:**
```cpp
auto matmul = a.matmul(b);
auto dot = a.dot(b);
auto norm = a.norm();
auto svd = a.svd();
auto eig = a.eig();
```

### 2.3 Indexing & Slicing

**Indexing:**
```cpp
auto tensor = torch::randn({10, 20, 30});

// Slicing
auto slice = tensor.index({Slice(0, 5), Slice(0, 10)});

// Advanced indexing
auto selected = tensor.index({torch::tensor({0, 2, 4})});

// Boolean masking
auto mask = tensor > 0.5;
auto masked = tensor.index({mask});
```

### 2.4 Shape Manipulation

**Reshape, View, Transpose:**
```cpp
auto tensor = torch::randn({2, 3, 4});

auto reshaped = tensor.reshape({6, 4});
auto viewed = tensor.view({-1, 4});  // Infer dimension
auto permuted = tensor.permute({2, 0, 1});
auto transposed = tensor.transpose(0, 1);

// Squeeze, unsqueeze
auto squeezed = tensor.squeeze();
auto unsqueezed = tensor.unsqueeze(0);
```

### 2.5 Device Management

**CPU ↔ GPU:**
```cpp
// Create on CPU
auto cpu_tensor = torch::randn({1000, 1000});

// Move to GPU
auto gpu_tensor = cpu_tensor.to(torch::kCUDA);

// Or create directly on GPU
auto direct_gpu = torch::randn({1000, 1000}, torch::kCUDA);

// Multi-GPU
auto gpu0 = torch::randn({100}, torch::Device(torch::kCUDA, 0));
auto gpu1 = torch::randn({100}, torch::Device(torch::kCUDA, 1));
```

---

## 3. Python Interop

### 3.1 CPython C API

**Embedding Python:**
```c
#include <Python.h>

// Initialize Python interpreter
Py_Initialize();

// Import module
PyObject* module = PyImport_ImportModule("torch");
PyObject* tensor_class = PyObject_GetAttrString(module, "Tensor");

// Call function
PyObject* args = PyTuple_Pack(1, PyLong_FromLong(10));
PyObject* result = PyObject_CallObject(tensor_class, args);

// Cleanup
Py_DECREF(result);
Py_DECREF(args);
Py_Finalize();
```

**Challenges:**
- Manual reference counting (Py_INCREF/Py_DECREF)
- Global Interpreter Lock (GIL)
- Type marshalling
- Error handling

### 3.2 PyO3-like Binding Approach

**Rust's PyO3 Pattern:**
```rust
// Rust example - Simple would be similar
use pyo3::prelude::*;

#[pyfunction]
fn train_model(data: &PyList) -> PyResult<Py<PyAny>> {
    Python::with_gil(|py| {
        let torch = py.import("torch")?;
        let nn = py.import("torch.nn")?;

        // Create model
        let model = nn.getattr("Linear")?.call1((784, 10))?;

        // Training logic...

        Ok(model.into())
    })
}
```

**Simple Translation:**
```simple
import simple.python

fn train_model(data: python.List) -> python.Object:
    python.with_gil(|py| {
        torch = py.import("torch")
        nn = py.import("torch.nn")

        # Create model
        model = nn.Linear(784, 10)

        # Training logic...

        return model
    })
```

### 3.3 DLPack Zero-Copy Protocol

**DLPack Specification:**
- Standard for tensor interchange
- Zero-copy between frameworks
- Supported by PyTorch, JAX, TensorFlow, NumPy, etc.

**C API:**
```c
// DLPack tensor descriptor
typedef struct {
    void* data;
    DLDevice device;
    int ndim;
    DLDataType dtype;
    int64_t* shape;
    int64_t* strides;
    uint64_t byte_offset;
} DLTensor;

// Producer exports DLPack
DLManagedTensor* to_dlpack(Tensor tensor);

// Consumer imports DLPack
Tensor from_dlpack(DLManagedTensor* dl_tensor);
```

**PyTorch Usage:**
```cpp
// C++ LibTorch
auto tensor = torch::randn({10, 20}, torch::kCUDA);

// Export to DLPack
auto dl_tensor = torch::utils::to_dlpack(tensor);

// Import in Python (zero-copy!)
```

```python
# Python
import torch.utils.dlpack as dlpack

# Import from C++
python_tensor = dlpack.from_dlpack(cpp_dl_tensor)

# Same memory!
assert python_tensor.data_ptr() == cpp_tensor.data_ptr()
```

---

## 4. Simple Language Integration

### 4.1 Tensor Type Design

**Core Tensor Type:**
```simple
# Simple tensor type
struct Tensor<T, Shape>:
    data_ptr: *mut T
    shape: Shape
    strides: Array<Int>
    device: Device
    requires_grad: Bool

enum Device:
    CPU
    CUDA(device_id: Int32)
    Vulkan(device_id: Int32)

# Type-safe shapes (optional)
type ImageTensor = Tensor<Float32, [Batch, 3, 224, 224]>
type WeightMatrix = Tensor<Float32, [InFeatures, OutFeatures]>
```

**Creation Functions:**
```simple
import simple.ml.torch

# Factory functions
let zeros = torch.zeros<Float32>([3, 4])
let ones = torch.ones<Float32>([3, 4], device: Device.CUDA(0))
let randn = torch.randn<Float32>([100, 100])

# From Simple arrays
let data = Array<Float32>::from([1.0, 2.0, 3.0, 4.0])
let tensor = torch.from_array(data, shape: [2, 2])

# Type-safe construction
let image: ImageTensor = torch.zeros([32, 3, 224, 224])
```

### 4.2 Autograd Integration

**Computation Graph:**
```simple
# Enable gradients
let x = torch.randn<Float32>([2, 2], requires_grad: true)
let y = x + 2.0
let z = y * y * 3.0
let out = z.mean()

# Backward pass
out.backward()

# Access gradients
print(x.grad())  # Option<Tensor>
```

**Custom Autograd Functions:**
```simple
# Define custom differentiable function
class CustomFunction:
    @[static]
    fn forward(ctx: Context, input: Tensor<Float32>) -> Tensor<Float32>:
        ctx.save_for_backward([input])
        return input * 2.0

    @[static]
    fn backward(ctx: Context, grad_output: Tensor<Float32>) -> Tensor<Float32>:
        input = ctx.saved_tensors[0]
        return grad_output * 2.0

# Use custom function
let y = CustomFunction.apply(x)
```

### 4.3 Neural Network Modules

**Module System:**
```simple
# Base module trait
trait Module<Input, Output>:
    fn forward(self: mut Self, input: Input) -> Output
    fn parameters(self: Self) -> Array<Tensor<Float32>>
    fn train(self: mut Self)
    fn eval(self: mut Self)

# Linear layer
class Linear(Module<Tensor<Float32>, Tensor<Float32>>):
    weight: Tensor<Float32>
    bias: Option<Tensor<Float32>>
    in_features: Int
    out_features: Int

    fn init(in_features: Int, out_features: Int, bias: Bool = true):
        self.in_features = in_features
        self.out_features = out_features
        self.weight = torch.randn([out_features, in_features])

        if bias:
            self.bias = Some(torch.zeros([out_features]))
        else:
            self.bias = None

    fn forward(input: Tensor<Float32>) -> Tensor<Float32>:
        output = input.matmul(self.weight.t())

        if let Some(bias) = self.bias:
            output = output + bias

        return output

    fn parameters() -> Array<Tensor<Float32>>:
        if let Some(bias) = self.bias:
            return [self.weight, bias]
        else:
            return [self.weight]
```

**Sequential Models:**
```simple
# Sequential container
class Sequential(Module<Tensor<Float32>, Tensor<Float32>>):
    layers: Array<Box<dyn Module<Tensor<Float32>, Tensor<Float32>>>>

    fn add_layer<M: Module<Tensor<Float32>, Tensor<Float32>>>(layer: M):
        self.layers.push(Box::new(layer))

    fn forward(input: Tensor<Float32>) -> Tensor<Float32>:
        output = input

        for layer in self.layers:
            output = layer.forward(output)

        return output

# Usage
let model = Sequential()
model.add_layer(Linear(784, 128))
model.add_layer(ReLU())
model.add_layer(Linear(128, 10))
```

**Full Model Example:**
```simple
class NeuralNet(Module<Tensor<Float32>, Tensor<Float32>>):
    fc1: Linear
    fc2: Linear
    dropout: Dropout

    fn init():
        self.fc1 = Linear(784, 128)
        self.fc2 = Linear(128, 10)
        self.dropout = Dropout(0.2)

    fn forward(x: Tensor<Float32>) -> Tensor<Float32>:
        x = self.fc1.forward(x)
        x = torch.relu(x)
        x = self.dropout.forward(x)
        x = self.fc2.forward(x)
        return torch.log_softmax(x, dim: 1)

    fn parameters() -> Array<Tensor<Float32>>:
        return self.fc1.parameters() + self.fc2.parameters()
```

### 4.4 Optimizers

**Optimizer Trait:**
```simple
trait Optimizer:
    fn step(self: mut Self)
    fn zero_grad(self: mut Self)
    fn state_dict(self: Self) -> Dict<String, Any>
    fn load_state_dict(self: mut Self, state: Dict<String, Any>)

# SGD implementation
class SGD(Optimizer):
    params: Array<Tensor<Float32>>
    lr: Float32
    momentum: Float32
    velocity: Array<Tensor<Float32>>  # Momentum buffers

    fn init(params: Array<Tensor<Float32>>, lr: Float32, momentum: Float32 = 0.0):
        self.params = params
        self.lr = lr
        self.momentum = momentum
        self.velocity = params.map(|p| torch.zeros_like(p))

    fn step():
        for i in 0..self.params.len():
            param = self.params[i]
            grad = param.grad().unwrap()

            if self.momentum > 0.0:
                # Update velocity
                self.velocity[i] = self.momentum * self.velocity[i] + grad

                # Update params with velocity
                param.data -= self.lr * self.velocity[i]
            else:
                # Simple gradient descent
                param.data -= self.lr * grad

    fn zero_grad():
        for param in self.params:
            if let Some(grad) = param.grad():
                grad.zero_()

# Adam optimizer
class Adam(Optimizer):
    params: Array<Tensor<Float32>>
    lr: Float32
    beta1: Float32
    beta2: Float32
    eps: Float32
    m: Array<Tensor<Float32>>  # First moment
    v: Array<Tensor<Float32>>  # Second moment
    t: Int  # Timestep

    fn step():
        self.t += 1

        for i in 0..self.params.len():
            param = self.params[i]
            grad = param.grad().unwrap()

            # Update biased first moment estimate
            self.m[i] = self.beta1 * self.m[i] + (1.0 - self.beta1) * grad

            # Update biased second moment estimate
            self.v[i] = self.beta2 * self.v[i] + (1.0 - self.beta2) * grad * grad

            # Bias correction
            m_hat = self.m[i] / (1.0 - self.beta1.pow(self.t))
            v_hat = self.v[i] / (1.0 - self.beta2.pow(self.t))

            # Update parameters
            param.data -= self.lr * m_hat / (v_hat.sqrt() + self.eps)
```

### 4.5 Training Loop

**Simple Training Example:**
```simple
import simple.ml.torch as torch
import simple.ml.data as data

# Load dataset
let train_data = data.MNIST(root: "data", train: true, download: true)
let train_loader = data.DataLoader(train_data, batch_size: 64, shuffle: true)

# Create model
let model = NeuralNet()

# Create optimizer
let optimizer = Adam(model.parameters(), lr: 0.001)

# Training loop
fn train_epoch(epoch: Int):
    model.train()

    for batch_idx, (batch_data, batch_target) in train_loader.enumerate():
        # Zero gradients
        optimizer.zero_grad()

        # Forward pass
        output = model.forward(batch_data)

        # Compute loss
        loss = torch.nll_loss(output, batch_target)

        # Backward pass
        loss.backward()

        # Update weights
        optimizer.step()

        if batch_idx % 100 == 0:
            print(f"Epoch {epoch}, Batch {batch_idx}, Loss: {loss.item()}")

# Train for 10 epochs
for epoch in 1..11:
    train_epoch(epoch)
```

---

## 5. FFI Architecture

### 5.1 LibTorch FFI Bindings

**C++ Wrapper Layer:**
```cpp
// simple_torch_ffi.cpp
#include <torch/torch.h>

extern "C" {

// Tensor creation
void* simple_torch_zeros(int64_t* shape, int ndim, int dtype, int device) {
    auto options = torch::TensorOptions()
        .dtype(static_cast<torch::ScalarType>(dtype))
        .device(static_cast<torch::Device>(device));

    std::vector<int64_t> shape_vec(shape, shape + ndim);
    auto tensor = torch::zeros(shape_vec, options);

    // Return owning pointer
    return new torch::Tensor(tensor);
}

// Tensor operations
void* simple_torch_add(void* a, void* b) {
    auto* tensor_a = static_cast<torch::Tensor*>(a);
    auto* tensor_b = static_cast<torch::Tensor*>(b);

    auto result = *tensor_a + *tensor_b;
    return new torch::Tensor(result);
}

// Autograd
void simple_torch_backward(void* tensor) {
    auto* t = static_cast<torch::Tensor*>(tensor);
    t->backward();
}

// Cleanup
void simple_torch_free_tensor(void* tensor) {
    delete static_cast<torch::Tensor*>(tensor);
}

}  // extern "C"
```

**Simple FFI Declarations:**
```simple
# simple/std_lib/src/ml/torch/ffi.spl

@[extern_c]
fn simple_torch_zeros(
    shape: *Int64,
    ndim: Int32,
    dtype: Int32,
    device: Int32
) -> *Void

@[extern_c]
fn simple_torch_add(a: *Void, b: *Void) -> *Void

@[extern_c]
fn simple_torch_backward(tensor: *Void)

@[extern_c]
fn simple_torch_free_tensor(tensor: *Void)
```

**Safe Wrapper:**
```simple
# simple/std_lib/src/ml/torch/tensor.spl

class Tensor<T>:
    ptr: *Void  # Owning pointer to torch::Tensor

    fn zeros(shape: Array<Int>) -> Tensor<T>:
        ptr = ffi.simple_torch_zeros(
            shape.as_ptr(),
            shape.len() as Int32,
            dtype_code<T>(),
            Device.CPU.to_int()
        )

        return Tensor { ptr }

    fn add(other: Tensor<T>) -> Tensor<T>:
        result_ptr = ffi.simple_torch_add(self.ptr, other.ptr)
        return Tensor { ptr: result_ptr }

    fn backward():
        ffi.simple_torch_backward(self.ptr)

    fn drop():
        ffi.simple_torch_free_tensor(self.ptr)
```

### 5.2 DLPack Bridge

**DLPack Exports:**
```simple
# simple/std_lib/src/ml/torch/dlpack.spl

@[extern_c]
struct DLManagedTensor:
    dl_tensor: DLTensor
    manager_ctx: *Void
    deleter: fn(*DLManagedTensor)

@[extern_c]
fn simple_torch_to_dlpack(tensor: *Void) -> *DLManagedTensor

@[extern_c]
fn simple_torch_from_dlpack(dl_tensor: *DLManagedTensor) -> *Void

# High-level API
class Tensor<T>:
    fn to_dlpack() -> *DLManagedTensor:
        return simple_torch_to_dlpack(self.ptr)

    @[static]
    fn from_dlpack(dl_tensor: *DLManagedTensor) -> Tensor<T>:
        ptr = simple_torch_from_dlpack(dl_tensor)
        return Tensor { ptr }
```

**Usage with Python:**
```simple
import simple.ml.torch as torch
import simple.python as py

# Create tensor in Simple
let simple_tensor = torch.randn<Float32>([100, 100])

# Export to DLPack
let dlpack = simple_tensor.to_dlpack()

# Import in Python (zero-copy!)
py.with_gil(|py_ctx| {
    torch_py = py_ctx.import("torch")
    dlpack_mod = py_ctx.import("torch.utils.dlpack")

    # Zero-copy import
    py_tensor = dlpack_mod.from_dlpack(dlpack)

    # Use in Python
    result = torch_py.matmul(py_tensor, py_tensor.t())

    # Export back to Simple
    result_dlpack = dlpack_mod.to_dlpack(result)
    simple_result = torch.Tensor.from_dlpack(result_dlpack)
})
```

### 5.3 Python Bridge (for Ecosystem)

**When to Use Python:**
- Loading pretrained models
- Using datasets (torchvision, etc.)
- Accessing new features not yet in LibTorch
- Debugging/prototyping

**Python Call Infrastructure:**
```simple
import simple.python as py

class PyTorchBridge:
    py_torch: py.Module

    fn init():
        py.initialize()
        self.py_torch = py.import("torch")

    fn load_pretrained_model(model_name: String) -> py.Object:
        torchvision = py.import("torchvision.models")
        model = torchvision.call_method(model_name, pretrained: true)
        return model

    fn run_python_model(model: py.Object, input_tensor: Tensor<Float32>) -> Tensor<Float32>:
        # Export Simple tensor to DLPack
        dlpack = input_tensor.to_dlpack()

        # Import in Python
        py_input = self.py_torch.from_dlpack(dlpack)

        # Run model
        py_output = model.call_method("forward", py_input)

        # Export back to Simple
        output_dlpack = py_output.call_method("to_dlpack")
        return Tensor::from_dlpack(output_dlpack)
```

---

## 6. Advanced Features

### 6.1 Distributed Training

**Multi-GPU Training:**
```simple
import simple.ml.torch.distributed as dist

# Initialize process group
dist.init_process_group(
    backend: "nccl",  # NVIDIA GPUs
    rank: process_rank,
    world_size: num_gpus
)

# Wrap model for data parallelism
let model = NeuralNet()
let ddp_model = dist.DistributedDataParallel(
    model,
    device_ids: [local_rank]
)

# Training loop (same as before)
for batch in train_loader:
    optimizer.zero_grad()
    output = ddp_model.forward(batch.data)
    loss = criterion(output, batch.target)
    loss.backward()
    optimizer.step()
```

**Gradient Synchronization:**
```simple
# All-reduce gradients across GPUs
dist.all_reduce(gradients, op: dist.ReduceOp.SUM)
gradients /= world_size
```

### 6.2 Mixed Precision Training

**Automatic Mixed Precision (AMP):**
```simple
import simple.ml.torch.amp as amp

let model = NeuralNet()
let optimizer = Adam(model.parameters())

# Create GradScaler for loss scaling
let scaler = amp.GradScaler()

for batch in train_loader:
    optimizer.zero_grad()

    # Forward pass in mixed precision
    with amp.autocast():
        output = model.forward(batch.data)
        loss = criterion(output, batch.target)

    # Scaled backward pass
    scaler.scale(loss).backward()

    # Unscale and step
    scaler.step(optimizer)
    scaler.update()
```

### 6.3 Custom CUDA Kernels

**Integration with Simple's GPU Support:**
```simple
import simple.gpu.cuda

# Custom CUDA kernel in Simple
@[cuda_kernel]
fn custom_relu_forward(input: Tensor<Float32>, output: mut Tensor<Float32>):
    idx = get_thread_id()
    output[idx] = max(0.0, input[idx])

@[cuda_kernel]
fn custom_relu_backward(grad_output: Tensor<Float32>, input: Tensor<Float32>, grad_input: mut Tensor<Float32>):
    idx = get_thread_id()
    grad_input[idx] = if input[idx] > 0.0 { grad_output[idx] } else { 0.0 }

# Wrap in autograd function
class CustomReLU:
    @[static]
    fn forward(ctx: Context, input: Tensor<Float32>) -> Tensor<Float32>:
        ctx.save_for_backward([input])

        output = torch.empty_like(input)
        custom_relu_forward<<<blocks, threads>>>(input, output)

        return output

    @[static]
    fn backward(ctx: Context, grad_output: Tensor<Float32>) -> Tensor<Float32>:
        input = ctx.saved_tensors[0]

        grad_input = torch.empty_like(input)
        custom_relu_backward<<<blocks, threads>>>(grad_output, input, grad_input)

        return grad_input
```

### 6.4 TorchScript Export

**Export Simple Models:**
```simple
# Train model in Simple
let model = NeuralNet()
train(model)

# Export to TorchScript
model.to_torchscript("model.pt")

# Can now load in Python or C++ LibTorch
```

---

## 7. Use Cases & Applications

### 7.1 Computer Vision

**Image Classification:**
```simple
import simple.ml.torch as torch
import simple.ml.vision as vision

# Load pretrained ResNet
let model = vision.models.resnet50(pretrained: true)
model.eval()

# Load image
let image = vision.io.read_image("image.jpg")
let preprocessed = vision.transforms.compose([
    vision.transforms.Resize(256),
    vision.transforms.CenterCrop(224),
    vision.transforms.ToTensor(),
    vision.transforms.Normalize(
        mean: [0.485, 0.456, 0.406],
        std: [0.229, 0.224, 0.225]
    ),
])(image)

# Inference
let output = model.forward(preprocessed.unsqueeze(0))
let class_idx = output.argmax(dim: 1)
print(f"Predicted class: {class_idx}")
```

### 7.2 Natural Language Processing

**Transformer Model:**
```simple
class TransformerBlock(Module):
    attention: MultiHeadAttention
    ffn: FeedForward
    norm1: LayerNorm
    norm2: LayerNorm

    fn forward(x: Tensor<Float32>) -> Tensor<Float32>:
        # Self-attention with residual
        attn_output = self.attention.forward(x)
        x = self.norm1.forward(x + attn_output)

        # Feed-forward with residual
        ffn_output = self.ffn.forward(x)
        x = self.norm2.forward(x + ffn_output)

        return x

# BERT-like model
class BERTModel(Module):
    embedding: Embedding
    blocks: Array<TransformerBlock>
    pooler: Linear

    fn forward(input_ids: Tensor<Int64>) -> Tensor<Float32>:
        # Embed
        x = self.embedding.forward(input_ids)

        # Transformer blocks
        for block in self.blocks:
            x = block.forward(x)

        # Pool (CLS token)
        pooled = self.pooler.forward(x[:, 0, :])

        return pooled
```

### 7.3 Reinforcement Learning

**DQN (Deep Q-Network):**
```simple
class DQN(Module):
    network: Sequential

    fn forward(state: Tensor<Float32>) -> Tensor<Float32>:
        return self.network.forward(state)

# Training
let q_network = DQN()
let target_network = DQN()
target_network.load_state_dict(q_network.state_dict())

let optimizer = Adam(q_network.parameters(), lr: 0.001)
let replay_buffer = ReplayBuffer(capacity: 10000)

for episode in 0..1000:
    state = env.reset()

    for step in 0..max_steps:
        # Epsilon-greedy action selection
        if random() < epsilon:
            action = env.action_space.sample()
        else:
            q_values = q_network.forward(state)
            action = q_values.argmax()

        # Step environment
        next_state, reward, done = env.step(action)

        # Store transition
        replay_buffer.push(state, action, reward, next_state, done)

        # Sample batch and train
        if replay_buffer.len() > batch_size:
            batch = replay_buffer.sample(batch_size)

            # Compute Q-learning loss
            q_values = q_network.forward(batch.states)
            next_q_values = target_network.forward(batch.next_states)

            expected_q = batch.rewards + gamma * next_q_values.max(dim: 1) * (1 - batch.dones)
            loss = torch.mse_loss(q_values.gather(1, batch.actions), expected_q)

            # Update
            optimizer.zero_grad()
            loss.backward()
            optimizer.step()

        state = next_state

        if done:
            break

    # Update target network periodically
    if episode % target_update_freq == 0:
        target_network.load_state_dict(q_network.state_dict())
```

### 7.4 Generative Models

**Variational Autoencoder (VAE):**
```simple
class VAE(Module):
    encoder: Sequential
    fc_mu: Linear
    fc_logvar: Linear
    decoder: Sequential

    fn encode(x: Tensor<Float32>) -> (Tensor<Float32>, Tensor<Float32>):
        h = self.encoder.forward(x)
        mu = self.fc_mu.forward(h)
        logvar = self.fc_logvar.forward(h)
        return (mu, logvar)

    fn reparameterize(mu: Tensor<Float32>, logvar: Tensor<Float32>) -> Tensor<Float32>:
        std = (logvar * 0.5).exp()
        eps = torch.randn_like(std)
        return mu + eps * std

    fn decode(z: Tensor<Float32>) -> Tensor<Float32>:
        return self.decoder.forward(z)

    fn forward(x: Tensor<Float32>) -> (Tensor<Float32>, Tensor<Float32>, Tensor<Float32>):
        mu, logvar = self.encode(x)
        z = self.reparameterize(mu, logvar)
        recon = self.decode(z)
        return (recon, mu, logvar)

# Loss function
fn vae_loss(recon: Tensor<Float32>, x: Tensor<Float32>, mu: Tensor<Float32>, logvar: Tensor<Float32>) -> Tensor<Float32>:
    # Reconstruction loss
    recon_loss = torch.binary_cross_entropy(recon, x, reduction: "sum")

    # KL divergence
    kl_div = -0.5 * (1 + logvar - mu.pow(2) - logvar.exp()).sum()

    return recon_loss + kl_div
```

---

## 8. Performance Considerations

### 8.1 Memory Management

**Tensor Lifecycle:**
```simple
# Simple's GC vs PyTorch's reference counting
class TensorWrapper:
    torch_tensor: *Void  # Raw pointer to torch::Tensor

    fn drop():
        # Explicit cleanup
        ffi.simple_torch_free_tensor(self.torch_tensor)

# Or use reference counting wrapper
class RcTensor<T>:
    inner: Rc<TensorWrapper>  # Reference counted

    fn clone() -> RcTensor<T>:
        return RcTensor { inner: self.inner.clone() }
```

**Memory Pooling:**
```simple
# Preallocate tensors to avoid allocation overhead
class TensorPool:
    free_tensors: Array<Tensor<Float32>>

    fn get_tensor(shape: Array<Int>) -> Tensor<Float32>:
        if let Some(tensor) = self.free_tensors.pop():
            if tensor.shape() == shape:
                return tensor

        # Allocate new tensor
        return torch.empty(shape)

    fn return_tensor(tensor: Tensor<Float32>):
        self.free_tensors.push(tensor)
```

### 8.2 CPU ↔ GPU Transfer Minimization

**Pinned Memory:**
```simple
# Allocate pinned (page-locked) memory for faster transfers
let cpu_tensor = torch.empty([1000, 1000], pinned: true)

# Transfer to GPU (faster with pinned memory)
let gpu_tensor = cpu_tensor.to(Device.CUDA(0))
```

**Async Transfers:**
```simple
# Non-blocking GPU transfer
let stream = torch.cuda.Stream()

with stream:
    gpu_tensor = cpu_tensor.to(Device.CUDA(0), non_blocking: true)

# Overlap with other work
do_cpu_work()

# Sync before using gpu_tensor
stream.synchronize()
```

### 8.3 Kernel Fusion

**Operation Fusion:**
```simple
# Manual fusion
fn fused_relu_add(a: Tensor<Float32>, b: Tensor<Float32>) -> Tensor<Float32>:
    # Single kernel: out = max(0, a + b)
    return torch.relu(a + b)  # PyTorch fuses internally

# Custom fused kernel
@[cuda_kernel]
fn fused_relu_add_kernel(a: Tensor<Float32>, b: Tensor<Float32>, out: mut Tensor<Float32>):
    idx = get_thread_id()
    out[idx] = max(0.0, a[idx] + b[idx])
```

### 8.4 Benchmarks (Expected)

**Target Performance:**
- FFI overhead: < 1% for large tensors (>1M elements)
- DLPack zero-copy: ~100 ns overhead
- Python bridge: 1-10 μs per call
- Training loop: Within 5% of native PyTorch

---

## 9. Implementation Plan

### Phase 1: LibTorch Core (Months 1-3)

**M1.1: FFI Bindings (Month 1)**
- Wrap core tensor operations (100+ functions)
- Tensor creation, indexing, arithmetic
- Device management (CPU/CUDA)
- Build system integration (link libtorch)

**M1.2: Autograd (Month 2)**
- Backward pass support
- Gradient accumulation
- Custom autograd functions
- Gradient checkpointing

**M1.3: Neural Network Modules (Month 3)**
- Module trait and base class
- Linear, Conv2d, RNN, LSTM
- BatchNorm, Dropout
- Sequential container

### Phase 2: Training Infrastructure (Months 4-5)

**M2.1: Optimizers (Month 4)**
- SGD, Adam, AdamW
- Learning rate schedulers
- Gradient clipping

**M2.2: Data Loading (Month 5)**
- Dataset trait
- DataLoader (batching, shuffling)
- Common datasets (MNIST, CIFAR-10)
- Data augmentation

### Phase 3: Python Bridge (Month 6)

**M3.1: CPython Embedding**
- Initialize Python runtime
- Call Python functions from Simple
- Handle exceptions

**M3.2: DLPack Integration**
- Export Simple tensors
- Import Python tensors
- Zero-copy validation

**M3.3: Ecosystem Access**
- Load pretrained models
- Use torchvision, transformers libraries
- Export models to ONNX

### Phase 4: Advanced Features (Months 7-9)

**M4.1: Distributed Training (Month 7)**
- Multi-GPU data parallelism
- Gradient synchronization
- Process group management

**M4.2: Mixed Precision (Month 8)**
- AMP API
- Loss scaling
- FP16/BF16 support

**M4.3: Custom Kernels (Month 9)**
- CUDA kernel integration
- Vulkan compute shaders
- Performance optimization

---

## 10. Documentation & Examples

### 10.1 Getting Started

```markdown
# Getting Started with PyTorch in Simple

## Installation

1. Install PyTorch (for LibTorch):
```bash
# Download LibTorch from pytorch.org
wget https://download.pytorch.org/libtorch/cu121/libtorch-cxx11-abi-shared-with-deps-2.5.0%2Bcu121.zip
unzip libtorch-*.zip
```

2. Install Simple compiler:
```bash
cargo install simple-lang
```

3. Create project:
```bash
simple new --template ml-project my_ml_project
cd my_ml_project
```

## First Model

```simple
# main.spl
import simple.ml.torch as torch

# Define model
class SimpleNet:
    fc1: torch.nn.Linear
    fc2: torch.nn.Linear

    fn init():
        self.fc1 = torch.nn.Linear(784, 128)
        self.fc2 = torch.nn.Linear(128, 10)

    fn forward(x: torch.Tensor<Float32>) -> torch.Tensor<Float32>:
        x = torch.relu(self.fc1.forward(x))
        x = self.fc2.forward(x)
        return x

# Train
let model = SimpleNet()
let optimizer = torch.optim.Adam(model.parameters(), lr: 0.001)

# ... training loop ...
```
```

### 10.2 Example Projects

1. **MNIST Classification**
   - Fully connected network
   - Training from scratch
   - Evaluation and metrics

2. **Image Classification (Transfer Learning)**
   - Load pretrained ResNet
   - Fine-tune on custom dataset
   - Data augmentation

3. **Text Classification**
   - Word embeddings
   - LSTM network
   - Sequence processing

4. **GAN (Generative Adversarial Network)**
   - Generator and discriminator
   - Adversarial training
   - Image generation

---

## 11. Conclusion & Recommendations

### Recommended Implementation Order:

1. **Phase 1: LibTorch Core (3 months)**
   - FFI bindings for tensors
   - Autograd support
   - Basic neural network modules

2. **Phase 2: Training Infrastructure (2 months)**
   - Optimizers and schedulers
   - Data loading utilities

3. **Phase 3: Python Bridge (1 month)**
   - CPython embedding
   - DLPack zero-copy
   - Ecosystem integration

4. **Phase 4: Advanced Features (3 months)**
   - Distributed training
   - Mixed precision
   - Custom CUDA kernels

### Success Metrics:

- API ergonomics (developer survey)
- Performance within 5% of Python PyTorch
- Zero-copy tensor operations working
- Type safety prevents common bugs
- 100+ neural network modules implemented

### Next Steps:

1. Prototype FFI bindings (2 weeks)
2. Validate LibTorch linking (1 week)
3. Implement core tensor operations (1 month)
4. Benchmark performance vs Python
5. Gather community feedback
