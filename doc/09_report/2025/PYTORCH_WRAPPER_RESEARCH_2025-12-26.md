# PyTorch Wrapper Research Summary

**Date:** 2025-12-26
**Research Document:** [pytorch_wrapper_design.md](../research/pytorch_wrapper_design.md)

## Summary

Completed comprehensive research on PyTorch wrapper design for Simple language, covering architecture analysis, integration strategies, and implementation recommendations.

## Key Findings

### 1. PyTorch Architecture (2025)

**LibTorch C++ API:**
- Stable ABI for production deployment
- ATen tensor library foundation
- Autograd engine for automatic differentiation
- TorchScript deprecated → use `torch.compile` instead
- Distributed training with FSDP2, DTensor, DeviceMesh
- CUDA 12.3 support with improved memory management

**Reference Counting:**
- PyTorch uses intrusive reference counting
- Important for integration with Simple's GC

### 2. Python Interop Analysis

**CPython C API:**
- Direct embedding/extending capabilities
- Requires GIL management
- Manual reference counting
- CPython-specific (not portable)

**PyO3/Rust Pattern:**
- Lifetime tracking with smart pointers
- Type-safe bindings with macros
- Maturin build integration
- Demonstrated with tch-rs + pyo3-tch

**Julia's PyCall:**
- Zero-copy via DLPack protocol
- Large data structure sharing
- Bidirectional tensor exchange

### 3. Recommended Architecture

**Primary Approach:** Direct LibTorch FFI bindings

```
Simple Code
    ↓
LibTorch C++ API (FFI)
    ↓
ATen/Autograd/CUDA
    ↓
Hardware (CPU/GPU)
```

**Advantages:**
- No Python dependency at runtime
- Better performance (no interpreter overhead)
- Type safety at compile time
- Direct access to LibTorch features

**Optional Python Bridge:**
- For Python-specific features (torchvision, HuggingFace)
- Isolated from core API
- Clear documentation of dependency

### 4. Simple Language Integration

**Type System:**
```simple
# GC-managed tensors (default)
let t1: Tensor = Tensor.randn([3, 3])

# Unique ownership for RAII
let t2: &Tensor = new(&) Tensor.randn([3, 3])

# Semantic types
type TensorShape = List[i64]
type LearningRate = f64
```

**Effect System:**
```simple
# GPU operations as async
fn matmul_cuda(a: Tensor, b: Tensor) async -> Tensor

# Pure functions for autograd
fn cross_entropy(pred: Tensor, labels: Tensor) -> Tensor
```

**Actor Model for Distributed Training:**
```simple
actor TrainingWorker:
    state:
        model: MLP
        optimizer: Adam

    on TrainBatch(data: Tensor, labels: Tensor) async:
        # Forward, backward, all-reduce, update
        ...
```

### 5. Zero-Copy Data Sharing

**DLPack Protocol:**
- Industry standard for tensor interchange
- Zero-copy between PyTorch, JAX, TensorFlow, CuPy
- CPU and GPU device support
- Simple implementation via FFI

**Example:**
```simple
# Simple → PyTorch (zero-copy)
let simple_tensor = Tensor.randn([100, 100])
let torch_tensor = torch.from_dlpack(simple_tensor.to_dlpack())

# PyTorch → Simple (zero-copy)
let result = Tensor.from_dlpack(torch_tensor.to_dlpack())
```

### 6. Performance Considerations

**Optimization Strategies:**
1. Batch operations to minimize FFI overhead
2. Use torch.compile for kernel fusion
3. Respect memory layout (contiguous, channels-last)
4. Stream management for overlap
5. Persistent kernels for repeated operations

**GPU Integration:**
- Zero-copy tensor ↔ GPU buffer conversion
- Shared memory with LibTorch allocator
- CUDA stream interop

### 7. API Surface Design

**Core Components:**

1. **Tensor Operations** - Creation, arithmetic, shape ops, reductions
2. **Autograd** - Gradient tracking, backward pass, context managers
3. **Neural Networks** - Module trait, layers, activations, losses
4. **Optimizers** - SGD, Adam, parameter updates
5. **Data Loading** - Dataset trait, DataLoader with actors
6. **Serialization** - Checkpoints, ONNX export
7. **Distributed** - DDP, FSDP via actor model

**Error Handling:**
```simple
enum TorchError:
    ShapeMismatch(expected: TensorShape, got: TensorShape)
    DeviceMismatch(expected: Device, got: Device)
    OutOfMemory(requested: usize, available: usize)

fn matmul(a: Tensor, b: Tensor) -> Result[Tensor, TorchError]
```

## Implementation Priorities

**Phase 1: Core Tensor Operations** (Week 1-2)
- Tensor creation, basic ops, shape ops, reductions
- Device management, DLPack support

**Phase 2: Autograd** (Week 3-4)
- Gradient tracking, backward pass, context managers

**Phase 3: Neural Networks** (Week 5-6)
- Module trait, linear/conv layers, activations, losses

**Phase 4: Training Infrastructure** (Week 7-8)
- Optimizers, data loading, training loops, serialization

**Phase 5: Advanced Features** (Week 9-12)
- Distributed training, mixed precision, custom operators

**Phase 6: Optional Python Bridge** (Week 13+)
- CPython API bindings, torchvision/torchaudio integration

## Module Organization

```
simple/std_lib/src/torch/
├── __init__.spl
├── tensor.spl
├── autograd.spl
├── nn/              # Neural network modules
├── optim/           # Optimizers
├── data/            # Data loading
├── cuda/            # GPU support
├── distributed/     # Distributed training
├── ffi/             # Low-level FFI bindings
└── python_bridge/   # Optional Python interop
```

## References

Consulted 40+ documentation sources including:

- PyTorch official docs (C++ API, CUDA, distributed)
- CPython C API reference
- PyO3 and tch-rs projects
- DLPack specification
- Julia PyCall patterns
- Simple language specifications (GPU, memory, concurrency, FFI)

## Next Actions

1. Prototype core tensor API with LibTorch FFI
2. Benchmark against Python PyTorch
3. Implement DLPack for zero-copy interop
4. Design neural network module system
5. Test distributed training with actors
6. Document API and create tutorials

## Related Documents

- Research: [pytorch_wrapper_design.md](../research/pytorch_wrapper_design.md)
- Spec: [gpu_simd/README.md](../spec/gpu_simd/README.md)
- Spec: [memory.md](../spec/memory.md)
- Spec: [concurrency.md](../spec/concurrency.md)
- Spec: [ffi_abi.md](../spec/ffi_abi.md)

---

**Status:** Research Complete
**Estimated Implementation Time:** 12-16 weeks for full PyTorch wrapper
**Minimum Viable Product:** 4-6 weeks (core tensors + autograd + basic nn)
