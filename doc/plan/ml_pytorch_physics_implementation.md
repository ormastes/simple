# ML/PyTorch and Physics Engine Implementation Plan

**Date:** 2025-12-27
**Updated:** 2026-02-01
**Status:** In Progress

## Recent Updates (2026-02-01)

- **Tensor bridge implemented:** `math/tensor_bridge.spl` provides conversion between math types (Vec3, Mat4, etc.) and tensors. Currently placeholder implementations until torch imports are resolved.
- **Physics uses shared math:** `physics/core` re-exports from `math` module; `physics/gpu_batch.spl` uses `core.Vector3` (now `math.Vec3d`).

## Overview

Implement ML/PyTorch functionality and physics engine for Simple language with CUDA-based PyTorch backend.

## Architecture

### ML/PyTorch Module Structure

```
simple/std_lib/src/ml/
├── __init__.spl          # ML module root
├── torch/
│   ├── __init__.spl      # PyTorch wrapper root
│   ├── tensor.spl        # Tensor operations
│   ├── nn/
│   │   ├── __init__.spl  # Neural network module
│   │   ├── activation.spl # Activation functions
│   │   ├── linear.spl    # Linear/Dense layers
│   │   ├── conv.spl      # Convolutional layers
│   │   ├── dropout.spl   # Dropout layers
│   │   ├── module.spl    # Base Module class
│   │   └── sequential.spl # Sequential container
│   ├── optim/
│   │   ├── __init__.spl  # Optimizer module
│   │   ├── optimizer.spl # Base Optimizer class
│   │   ├── sgd.spl       # SGD optimizer
│   │   ├── adam.spl      # Adam optimizer
│   │   └── adamw.spl     # AdamW optimizer
│   └── autograd/
│       ├── __init__.spl  # Autograd module
│       └── function.spl  # Autograd functions
```

### Physics Engine Structure

```
simple/std_lib/src/physics/
├── __init__.spl          # Physics module root
├── core/
│   ├── __init__.spl      # Core physics
│   ├── vector.spl        # 2D/3D vectors (GPU-accelerated via PyTorch)
│   ├── matrix.spl        # Transformation matrices
│   └── quaternion.spl    # Rotation quaternions
├── dynamics/
│   ├── __init__.spl      # Dynamics module
│   ├── rigidbody.spl     # Rigid body physics
│   ├── forces.spl        # Force application
│   └── integrator.spl    # Physics integration (Euler, RK4, Verlet)
├── collision/
│   ├── __init__.spl      # Collision detection
│   ├── aabb.spl          # Axis-aligned bounding boxes
│   ├── shape.spl         # Collision shapes
│   └── detector.spl      # Collision detection algorithms
├── constraints/
│   ├── __init__.spl      # Constraint solver
│   ├── joint.spl         # Joint constraints
│   └── solver.spl        # Constraint solver
└── world.spl             # Physics world/scene

simple/std_lib/test/unit/ml/
└── torch/
    ├── tensor_spec.spl
    ├── nn/
    │   ├── activation_spec.spl
    │   ├── linear_spec.spl
    │   └── conv_spec.spl
    └── optim/
        ├── sgd_spec.spl
        └── adam_spec.spl

simple/std_lib/test/unit/physics/
├── core/
│   └── vector_spec.spl
├── dynamics/
│   └── rigidbody_spec.spl
└── collision/
    └── detector_spec.spl
```

## Implementation Phases

### Phase 1: ML/PyTorch Core (High Priority)

1. **Tensor Operations** (`ml/torch/tensor.spl`)
   - Device management (CPU/CUDA)
   - Tensor creation (zeros, ones, randn, arange)
   - Basic operations (add, sub, mul, div, matmul)
   - Shape operations (reshape, transpose, squeeze, unsqueeze)
   - Data transfer (to_cpu, to_cuda, copy)

2. **Neural Network Layers** (`ml/torch/nn/`)
   - Activation functions (ReLU, GELU, SiLU, Mish, etc.)
   - Linear layer (fully connected)
   - Conv2d layer
   - Dropout layer
   - Module base class
   - Sequential container

3. **Optimizers** (`ml/torch/optim/`)
   - Base Optimizer class
   - SGD (with momentum, weight decay)
   - Adam (adaptive learning rate)
   - AdamW (Adam with decoupled weight decay)

4. **Examples**
   - MNIST classifier
   - Simple CNN
   - Training loop example

### Phase 2: Physics Engine Core (High Priority)

1. **Core Math** (`physics/core/`)
   - Vector2/Vector3 with GPU acceleration
   - Matrix3/Matrix4 for transformations
   - Quaternion for rotations
   - All using PyTorch tensors for GPU acceleration

2. **Rigid Body Dynamics** (`physics/dynamics/`)
   - RigidBody class (position, velocity, acceleration, mass, inertia)
   - Force application (gravity, spring, damping)
   - Integration methods (Euler, RK4, Verlet)
   - Batch processing on GPU

3. **Collision Detection** (`physics/collision/`)
   - AABB (Axis-Aligned Bounding Box)
   - Sphere, Box, Capsule shapes
   - Broad phase (spatial hashing on GPU)
   - Narrow phase (SAT, GJK)

4. **Physics World** (`physics/world.spl`)
   - Scene management
   - Simulation loop
   - GPU batch processing
   - Object registration/removal

### Phase 3: Advanced Features (Medium Priority)

1. **ML Enhancements**
   - Batch normalization
   - Layer normalization
   - Attention mechanisms
   - RNN/LSTM/GRU layers
   - Transformer blocks

2. **Physics Enhancements**
   - Constraint solver (joints, springs)
   - Soft body physics
   - Fluid simulation (SPH)
   - Cloth simulation

## CUDA Integration

### Device Management Strategy

```simple
import ml.torch

fn main():
    # Auto-detect best device
    let device = if Tensor::cuda_available():
        Device::CUDA(0)  # Use GPU 0
    else:
        Device::CPU

    # Create tensors on device
    let x = Tensor::randn([1000, 1000], device=device)
    let y = Tensor::randn([1000, 1000], device=device)

    # Operations run on GPU
    let z = x @ y  # Matrix multiply on CUDA
```

### Performance Considerations

- Minimize CPU ↔ GPU transfers
- Batch operations on GPU
- Use contiguous tensors
- Leverage PyTorch's autograd for gradients
- Use mixed precision (FP16) where appropriate

## Testing Strategy

### ML Tests
- Unit tests for each layer/operation
- Gradient checking tests
- Shape verification tests
- Device transfer tests
- Training convergence tests

### Physics Tests
- Vector math accuracy tests
- Integration stability tests
- Collision detection accuracy tests
- Energy conservation tests
- GPU vs CPU comparison tests

## Dependencies

### Existing
- `src/runtime/src/value/torch.rs` - 139 FFI functions
- CUDA 13.0 with RTX A6000/TITAN RTX GPUs
- LibTorch 2.5.1+cu121

### Required
- PyTorch feature flag enabled
- CUDA-enabled LibTorch build
- Environment variable: `SIMPLE_PYTORCH_DEVICE=cuda`

## Example Usage

### ML Example: Simple Neural Network

```simple
import ml.torch as torch
import ml.torch.nn as nn
import ml.torch.optim as optim

class SimpleNet(nn.Module):
    fn __init__(self):
        super().__init__()
        self.fc1 = nn.Linear(784, 128)
        self.fc2 = nn.Linear(128, 10)
        self.relu = nn.ReLU()

    fn forward(self, x):
        x = self.relu(self.fc1(x))
        x = self.fc2(x)
        return x

fn main():
    # Create model on GPU
    let device = torch.Device::CUDA(0) if torch.cuda_available() else torch.Device::CPU
    let model = SimpleNet().to(device)
    let optimizer = optim.Adam(model.parameters(), lr=0.001)

    # Training loop
    for epoch in range(10):
        # Forward pass
        let output = model(inputs)
        let loss = nn.cross_entropy(output, labels)

        # Backward pass
        optimizer.zero_grad()
        loss.backward()
        optimizer.step()

        print(f"Epoch {epoch}, Loss: {loss.item()}")
```

### Physics Example: Particle Simulation

```simple
import physics
import physics.dynamics as dynamics
import physics.collision as collision

fn main():
    # Create physics world (GPU-accelerated)
    let world = physics.World(gravity=Vector3(0, -9.81, 0))

    # Create rigid bodies (batched on GPU)
    let bodies = []
    for i in range(1000):
        let body = dynamics.RigidBody(
            mass=1.0,
            position=Vector3(randn(), randn(), randn()),
            shape=collision.Sphere(radius=0.5)
        )
        world.add_body(body)
        bodies.push(body)

    # Simulation loop (GPU batch processing)
    for step in range(1000):
        world.step(dt=0.016)  # 60 FPS

        # GPU collision detection
        let collisions = world.detect_collisions()
        world.resolve_collisions(collisions)
```

## Implementation Notes

- Use CUDA for all heavy computations
- Batch operations for GPU efficiency
- Follow Simple language conventions
- Include comprehensive BDD tests
- Document all public APIs
- Profile GPU performance

## Success Criteria

1. ✅ ML module can train MNIST classifier on GPU
2. ✅ Physics engine can simulate 1000+ bodies at 60 FPS
3. ✅ All tests pass on both CPU and CUDA
4. ✅ API is simple and pythonic
5. ✅ GPU utilization > 80% during training/simulation
6. ✅ Documentation and examples complete

## Next Steps

1. Create ML module structure
2. Implement Tensor wrapper class
3. Implement NN layers
4. Implement optimizers
5. Create physics module structure
6. Implement vector/matrix math
7. Implement rigid body dynamics
8. Implement collision detection
9. Write comprehensive tests
10. Create examples and documentation
