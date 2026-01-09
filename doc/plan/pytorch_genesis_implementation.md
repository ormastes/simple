# Physics Engine & ML PyTorch Implementation Plan

**Date:** 2025-12-27
**Scope:** Full ML framework (PyTorch/LibTorch) + Genesis Physics Engine
**Timeline:** 37 weeks (9 months)
**User Choices:**
- ✅ PyTorch first → Full framework (tensors + autograd + NN + data loading)
- ✅ LibTorch C++ direct FFI (no Python dependency for ML)
- ✅ Genesis physics engine (Python FFI, after PyTorch)

---

## Overview

### What Exists (Strong Foundation)
1. **Vulkan GPU Backend** - Production-ready with 22 unit tests, handle-based registry pattern
2. **SIMD Operations** - 15+ vectorized array operations
3. **FFI Infrastructure** - 150+ runtime functions, proven integration patterns
4. **Actor System** - Message-passing concurrency for distributed workloads
5. **Unit Type System** - Foundation for physical quantities (needs expansion)
6. **Extensive Research** - 8000+ lines covering PyTorch, Genesis, game engines

### What's Missing (Implementation Gap)
- **0% ML Framework** - No tensor library, autograd, NN modules
- **0% Physics Engine** - No Genesis bindings, no simulation wrapper
- **Physical Units** - Need Force, Torque, Velocity, Mass, etc.

---

## Implementation Strategy

### Phase I: PyTorch ML Framework (Weeks 1-20)
**Goal:** Full-featured ML framework competitive with Python PyTorch

### Phase II: Genesis Physics Engine (Weeks 21-37)
**Goal:** Type-safe physics simulation with actor-based distribution

**Rationale for Sequencing:**
- Physics engines return tensors → PyTorch must exist first
- DLPack tensor sharing requires PyTorch foundation
- Policy networks consume physics observations as tensors

---

## PHASE I: PyTorch ML Framework (20 Weeks)

### Week 1-4: Core Tensor System

**Objectives:**
- Build LibTorch C++ integration with handle-based FFI
- Implement 50+ tensor operations
- Integrate with RuntimeValue system
- Memory management (GC integration)

**Key Deliverables:**
```simple
let a = Tensor::randn([100, 100])
let b = Tensor::ones([100, 100])
let c = a.matmul(b)
let gpu_tensor = c.to(Device::CUDA(0))
```

**Critical Files:**
- `src/runtime/src/value/torch.rs` (NEW) - FFI layer with TENSOR_REGISTRY
- `src/runtime/src/value/torch_ffi_wrapper.cpp` (NEW) - C++ LibTorch wrapper
- `src/runtime/Cargo.toml` - Add `tch = { version = "0.16", optional = true }`
- `src/compiler/src/codegen/runtime_ffi.rs` - Add tensor FFI specs
- `simple/std_lib/src/ml/torch/tensor.spl` (NEW) - Simple API wrapper

**Architecture Pattern (from Vulkan):**
```rust
lazy_static! {
    static ref TENSOR_REGISTRY: Mutex<HashMap<u64, Arc<TorchTensor>>> = Mutex::new(HashMap::new());
    static ref NEXT_HANDLE: AtomicU64 = AtomicU64::new(1);
}

#[no_mangle]
pub extern "C" fn rt_torch_zeros(shape_ptr: *const i64, ndim: i32, dtype: i32) -> u64 {
    // Create tensor, register handle, return u64
}
```

**Success Criteria:**
- ✅ Matrix multiply works: `C = A @ B`
- ✅ GPU transfer: `tensor.to(Device::CUDA(0))`
- ✅ No memory leaks (1000 allocations)
- ✅ Performance within 10% of LibTorch native

---

### Week 5-6: Autograd System

**Objectives:**
- Gradient tracking infrastructure
- backward() implementation
- Gradient accumulation

**Key Deliverables:**
```simple
let x = Tensor::ones([2, 2], requires_grad=true)
let y = x + 2
let z = y * y * 3
let out = z.mean()
out.backward()
let grad = x.grad()  // dy/dx
```

**Critical Files:**
- Update `src/runtime/src/value/torch.rs` - Add autograd FFI
- Update `src/runtime/src/value/torch_ffi_wrapper.cpp` - Wrap autograd API
- `simple/std_lib/src/ml/torch/autograd.spl` (NEW) - Autograd helpers

**Success Criteria:**
- ✅ Simple gradient computation: y = x², dy/dx = 2x
- ✅ Chain rule works: nested operations
- ✅ Gradient accumulation (multiple backward calls)

---

### Week 7-10: Neural Network Modules

**Objectives:**
- Module system foundation
- Core layers (Linear, Conv2d, RNN, LSTM)
- BatchNorm, Dropout, activations
- Model serialization (save/load)

**Key Deliverables:**
```simple
class MLP:
    fn __init__(self, input_dim: i32, hidden_dim: i32, output_dim: i32):
        self.fc1 = nn.Linear(input_dim, hidden_dim)
        self.fc2 = nn.Linear(hidden_dim, output_dim)

    fn forward(self, x: Tensor) -> Tensor:
        x = self.fc1.forward(x).relu()
        return self.fc2.forward(x)
```

**Critical Files:**
- `src/runtime/src/value/torch.rs` - Add module registry
- `simple/std_lib/src/ml/nn/__init__.spl` (NEW) - Module trait
- `simple/std_lib/src/ml/nn/linear.spl` (NEW) - Linear layer
- `simple/std_lib/src/ml/nn/conv.spl` (NEW) - Convolution layers
- `simple/std_lib/src/ml/nn/rnn.spl` (NEW) - Recurrent layers

**Success Criteria:**
- ✅ Define MLP with Sequential API
- ✅ Forward pass produces correct outputs
- ✅ Backward pass computes layer gradients
- ✅ Save/load model weights

---

### Week 11-14: Optimizers & Training

**Objectives:**
- SGD, Adam, AdamW optimizers
- Learning rate schedulers
- Loss functions (MSE, CrossEntropy, etc.)
- Complete MNIST training loop

**Key Deliverables:**
```simple
let model = MLP::new(784, 128, 10)
let optimizer = Adam::new(model.parameters(), lr=0.001)
let loss_fn = CrossEntropyLoss::new()

for epoch in 0..10:
    for (images, labels) in train_loader:
        let outputs = model.forward(images)
        let loss = loss_fn(outputs, labels)

        optimizer.zero_grad()
        loss.backward()
        optimizer.step()
```

**Critical Files:**
- `simple/std_lib/src/ml/optim/__init__.spl` (NEW) - Optimizer trait
- `simple/std_lib/src/ml/optim/sgd.spl` (NEW) - SGD optimizer
- `simple/std_lib/src/ml/optim/adam.spl` (NEW) - Adam/AdamW
- `simple/std_lib/src/ml/losses.spl` (NEW) - Loss functions
- `simple/std_lib/src/ml/metrics.spl` (NEW) - Accuracy, F1, etc.

**Success Criteria:**
- ✅ Train MLP on MNIST to >95% accuracy
- ✅ Optimizer reduces loss each step
- ✅ Performance within 10% of Python PyTorch

---

### Week 15-16: Data Loading

**Objectives:**
- Dataset trait
- DataLoader with batching/shuffling
- Common datasets (MNIST, CIFAR-10)
- Transform pipeline

**Key Deliverables:**
```simple
let dataset = MNIST::new("/data/mnist", train=true)
let loader = DataLoader::new(dataset, batch_size=64, shuffle=true)

for (images, labels) in loader:
    // images: Tensor<f32, [64, 1, 28, 28]>
    // labels: Tensor<i64, [64]>
```

**Critical Files:**
- `simple/std_lib/src/ml/data/__init__.spl` (NEW) - Dataset trait
- `simple/std_lib/src/ml/data/dataloader.spl` (NEW) - DataLoader
- `simple/std_lib/src/ml/data/datasets/mnist.spl` (NEW) - MNIST dataset
- `simple/std_lib/src/ml/data/transforms.spl` (NEW) - Image transforms

**Success Criteria:**
- ✅ Load MNIST with batching
- ✅ Shuffling works correctly
- ✅ Transforms apply (normalize, random crop, etc.)

---

### Week 17-18: GPU Integration

**Objectives:**
- Tensor ↔ Vulkan buffer conversion
- DLPack zero-copy protocol
- Custom SPIR-V kernels for operations
- GPU memory pooling

**Key Deliverables:**
```simple
// Zero-copy tensor → Vulkan buffer
let tensor = Tensor::randn([1024, 1024], device=Device::CUDA(0))
let vk_buffer = tensor.to_vulkan_buffer()

// Custom kernel
let custom_relu = compile_kernel("relu.spv")
custom_relu.launch(vk_buffer)

// Back to tensor (zero-copy)
let result = Tensor::from_vulkan_buffer(vk_buffer)
```

**Critical Files:**
- Update `src/runtime/src/value/torch.rs` - Add DLPack conversion
- Update `src/runtime/src/value/gpu_vulkan.rs` - Tensor interop
- `simple/std_lib/src/ml/torch/dlpack.spl` (NEW) - DLPack API

**Success Criteria:**
- ✅ Transfer 1GB tensor, verify zero-copy (no memory duplication)
- ✅ Custom ReLU kernel via Vulkan matches PyTorch accuracy
- ✅ Autograd works through custom kernels

---

### Week 19: Distributed Training

**Objectives:**
- Multi-GPU support with actors
- Gradient synchronization
- Data parallelism

**Key Deliverables:**
```simple
@actor
struct GPUWorker:
    model: MLP
    device: Device

    @async
    fn train_step(batch: Tensor) -> Tensor:
        // Forward + backward on GPU
        let loss = self.model.forward(batch).loss()
        loss.backward()
        return self.model.gradients()

// Spawn workers on 2 GPUs
let workers = [
    GPUWorker::spawn(Device::CUDA(0)),
    GPUWorker::spawn(Device::CUDA(1)),
]

// Distributed training
let grads = await_all(workers.map(|w| w.train_step(batch)))
let avg_grad = Tensor::mean(grads)
optimizer.apply_gradients(avg_grad)
```

**Critical Files:**
- `simple/std_lib/src/ml/distributed.spl` (NEW) - Multi-GPU helpers

**Success Criteria:**
- ✅ 2-GPU training achieves 1.8x speedup
- ✅ Gradients synchronized correctly

---

### Week 20: Polish & Documentation

**Objectives:**
- 5+ comprehensive examples
- 20+ integration tests
- API documentation
- Performance benchmarks

**Deliverables:**
- `simple/examples/ml/mnist_mlp.spl` - MLP training
- `simple/examples/ml/cifar10_cnn.spl` - CNN training
- `simple/examples/ml/lstm_text.spl` - LSTM text generation
- `simple/examples/ml/vae.spl` - Variational autoencoder
- `simple/examples/ml/dqn.spl` - Deep Q-Network (RL)

**Success Criteria:**
- ✅ All examples run successfully
- ✅ Documentation covers 90% of API
- ✅ Training performance within 5% of Python PyTorch

---

## PHASE II: Genesis Physics Engine (17 Weeks)

**Prerequisites:** Phase I complete (PyTorch tensors available)

### Week 21-23: Python Bridge Infrastructure

**Objectives:**
- CPython embedding layer
- Python↔Simple value conversion
- GIL management for thread safety
- DLPack integration with PyTorch tensors

**Key Deliverables:**
```simple
import sys.python

python.init()
let genesis = python.import_module("genesis")
let scene_class = genesis.get_attr("Scene")
let scene = scene_class.call([], {"num_envs": 16})
```

**Critical Files:**
- `src/runtime/src/value/python_bridge.rs` (NEW) - CPython FFI
- `src/runtime/Cargo.toml` - Add `pyo3 = "0.20"`
- `simple/std_lib/src/sys/python.spl` (NEW) - Python interop API

**Architecture:**
```rust
// GIL management
pub struct GilGuard(Option<Python<'static>>);

impl GilGuard {
    pub fn acquire() -> Self {
        GilGuard(Some(Python::acquire_gil().python()))
    }
}

// Value conversion
RuntimeValue::NIL ↔ None
RuntimeValue int ↔ int
RuntimeValue string ↔ str
RuntimeValue array ↔ list
Python object → opaque handle (RuntimeValue::HeapPtr)
```

**Success Criteria:**
- ✅ Initialize Python interpreter
- ✅ Call `print("Hello from Genesis!")`
- ✅ Zero-copy DLPack: PyTorch tensor ↔ NumPy array
- ✅ Graceful error handling for Python exceptions

---

### Week 24-26: Core Genesis Bindings

**Objectives:**
- Scene creation and management
- Entity API (primitives, URDF, MJCF)
- Sensor system (cameras, proprioception)
- Material and surface properties

**Key Deliverables:**
```simple
import physics.genesis.{Scene, Morph, Material}
import units.{Length, Density}

let scene = Scene::new(
    num_envs=16,
    timestep=#Duration::from_millis(10),
    gravity=Vec3::new(0, 0, -9.81).map(#Acceleration::from_m_s2)
)

let plane = scene.add_entity(Morph::Plane(Vec2::new(10, 10).map(#Length::from_meters)))
let robot = scene.add_entity(Morph::URDF("franka_panda.urdf"))

scene.build()
scene.step()
```

**Critical Files:**
- `src/runtime/src/value/genesis_physics.rs` (NEW) - Genesis FFI
- `simple/std_lib/src/physics/genesis/scene.spl` (NEW) - Scene API
- `simple/std_lib/src/physics/genesis/entity.spl` (NEW) - Entity API
- `simple/std_lib/src/physics/genesis/sensors.spl` (NEW) - Sensor API

**Architecture Pattern:**
```rust
lazy_static! {
    static ref SCENE_REGISTRY: Mutex<HashMap<u64, Arc<GenesisScene>>> = Mutex::new(HashMap::new());
}

#[repr(C)]
pub struct RuntimeGenesisScene {
    pub header: HeapHeader,
    pub py_scene: PyObject,  // Genesis Scene instance
    pub num_envs: i32,
}
```

**Success Criteria:**
- ✅ Create scene, add box, step 1000 times
- ✅ Box falls and settles due to gravity
- ✅ Camera renders RGB image (640x480)
- ✅ Read robot joint positions/velocities

---

### Week 27-29: Physics Solvers

**Objectives:**
- Rigid body dynamics (forces, torques, constraints)
- Soft body solvers (MPM, SPH, FEM, PBD)
- Solver coupling (rigid-fluid interaction)

**Key Deliverables:**
```simple
// Rigid body control
let torques = compute_pd_control(joint_pos, joint_vel)
robot.set_joint_torques(torques)

// SPH fluid simulation
let water = scene.add_soft_body(
    solver=SoftBodySolver::SPH(
        density=#Density::from_kg_m3(1000.0),
        viscosity=0.01
    ),
    initial_particles=create_water_cube(10000)
)

// Rigid-fluid coupling
scene.enable_coupling(CouplingConfig {
    solver_pair: (PhysicsSolver::Rigid, PhysicsSolver::SPH),
    stiffness: 1000.0
})
```

**Critical Files:**
- Update `simple/std_lib/src/physics/genesis/entity.spl` - Add force/torque API
- `simple/std_lib/src/physics/genesis/soft_body.spl` (NEW) - Soft body API
- `simple/std_lib/src/physics/genesis/coupling.spl` (NEW) - Solver coupling

**Success Criteria:**
- ✅ PD controller converges joints to zero position
- ✅ Water simulation (SPH) fills container
- ✅ Robot arm pushes water (rigid-fluid coupling)

---

### Week 30-31: Tensor Integration

**Objectives:**
- Batched observation API (all env states in single tensor)
- Batched action application
- DLPack zero-copy with PyTorch
- Enable differentiable physics (gradient flow)

**Key Deliverables:**
```simple
// Efficient batched observation
let obs_spec = ObservationSpec {
    joint_positions: true,
    joint_velocities: true,
    link_poses: ["end_effector"]
}
let obs = scene.observe(obs_spec)  // Tensor<f32, [4096, ObsDim]>

// Batched actions
let actions = policy.forward(obs)  // Tensor<f32, [4096, ActionDim]>
scene.apply_actions(actions, ActionSpec { mode: ActionMode::JointTorque })

// Differentiable physics
scene.enable_gradients(true)
scene.step()
let loss = compute_task_loss(robot)
scene.backward(loss)
assert(actions.grad().is_some())  // Gradients through physics!
```

**Critical Files:**
- Update `src/runtime/src/value/genesis_physics.rs` - Add batched APIs
- `simple/std_lib/src/physics/genesis/observation.spl` (NEW) - Obs API
- `simple/std_lib/src/physics/genesis/action.spl` (NEW) - Action API

**Success Criteria:**
- ✅ Batched observation for 4096 envs in <100μs
- ✅ Zero-copy verified (no GPU→CPU→GPU)
- ✅ Gradient flow: loss.backward() computes action gradients

---

### Week 32-33: Unit Type Safety

**Objectives:**
- Physical unit types (Force, Torque, Velocity, Mass, etc.)
- Dimensional analysis at compile time
- Unit conversions (imperial ↔ metric)
- Runtime validation contracts

**Key Deliverables:**
```simple
// Type-safe units
let force = Vec3::new(10.0, 0.0, 0.0).map(#Force::from_N)
let lever = Vec3::new(0.1, 0.0, 0.0).map(#Length::from_meters)
let torque = force.cross(lever)  // Returns Vec3<#Torque> automatically

// Dimensional analysis
fn apply_force(force: #Force, mass: #Mass) -> #Acceleration:
    // Force / Mass = Acceleration (compile-time checked!)
    return #Acceleration::from_m_s2(force.as_N() / mass.as_kg())

// COMPILE ERROR: Type mismatch
// robot.apply_torque("link", force)  // Cannot pass Force where Torque expected
```

**Critical Files:**
- `simple/std_lib/src/units/physical/__init__.spl` (NEW) - Physical unit types
- Update all Genesis APIs to use unit types instead of raw `f32`

**Unit Types to Add:**
- `#Force` (Newtons)
- `#Torque` (Newton-meters)
- `#Velocity` (meters/second)
- `#AngularVelocity` (radians/second)
- `#Acceleration` (meters/second²)
- `#Mass` (kilograms)
- `#Density` (kg/m³)
- `#Angle` (radians, with degree conversion)

**Success Criteria:**
- ✅ Compile error when passing Force instead of Torque
- ✅ Unit conversions work (imperial ↔ metric)
- ✅ Runtime validation prevents excessive forces (contract violations)

---

### Week 34-35: Actor-Based Distribution

**Objectives:**
- Parallel environment actors (multi-process)
- Gradient aggregation across actors
- Distributed rollout collection

**Key Deliverables:**
```simple
// 4 actors × 4096 envs = 16384 total envs
let envs = ParallelEnvs::new(
    num_actors=4,
    envs_per_actor=4096,
    config=SceneConfig { robot_urdf: "robot.urdf", ... }
)

// Parallel step (each actor on separate GPU)
let (obs, rewards, dones) = await envs.step(actions)
// obs: Tensor<f32, [16384, ObsDim]>

// Distributed backward
envs.backward(loss)  // Gradients aggregated across actors
```

**Critical Files:**
- `simple/std_lib/src/physics/genesis/env_actor.spl` (NEW) - Actor wrapper
- `simple/std_lib/src/physics/genesis/parallel.spl` (NEW) - Multi-actor coordinator

**Architecture:**
```simple
@actor
struct PhysicsEnvActor:
    scene: Scene
    robot: Articulation

    @async
    fn step(actions: Tensor) -> (Tensor, Tensor, Tensor):
        scene.apply_actions(actions)
        scene.step()
        let obs = scene.observe(ObservationSpec::default())
        let rewards = compute_rewards()
        let dones = check_termination()
        return (obs, rewards, dones)
```

**GIL Mitigation:**
- Each actor runs in separate process (via multiprocessing)
- Genesis releases GIL during GPU compute (Taichi kernels)
- Shared memory for tensor transfer (DLPack + shared storage)

**Success Criteria:**
- ✅ 16K environments across 4 GPUs
- ✅ Throughput: 1M+ FPS total
- ✅ Gradient correctness (vs single-GPU baseline)

---

### Week 36-37: High-Level API & Examples

**Objectives:**
- Gym-compatible Environment trait
- Pre-built environments (reaching, locomotion, manipulation)
- Curriculum learning
- Domain randomization
- Complete training examples

**Key Deliverables:**
```simple
// Pre-built environment
let env = FrankaReachEnv::new(num_envs=4096)

// Curriculum learning
env.set_difficulty(0.0)  // Easy: large targets, close to robot
for epoch in 0..1000:
    let buffer = collect_rollout(env, policy, steps=512)
    train_policy(buffer)

    let success_rate = buffer.info.mean("success")
    env.auto_adapt(success_rate)  // Auto-adjust difficulty

// Domain randomization
let dr_config = DomainRandomization {
    randomize_mass: true,
    mass_range: (0.8, 1.2),
    randomize_friction: true,
    friction_range: (0.5, 1.5),
}
env.apply_domain_randomization(dr_config)
```

**Critical Files:**
- `simple/std_lib/src/physics/genesis/env.spl` (NEW) - Environment trait
- `simple/std_lib/src/physics/genesis/envs/franka_reach.spl` (NEW) - Reaching task
- `simple/std_lib/src/physics/genesis/envs/ant_locomotion.spl` (NEW) - Quadruped
- `simple/std_lib/src/physics/genesis/curriculum.spl` (NEW) - Curriculum API
- `simple/std_lib/src/physics/genesis/randomization.spl` (NEW) - Domain randomization

**Pre-built Environments:**
1. **FrankaReachEnv** - Robot arm reaching target
2. **AntLocomotionEnv** - Quadruped walking
3. **HumanoidStandupEnv** - Humanoid balance
4. **ShadowHandManipulateEnv** - Dexterous manipulation
5. **QuadrotorHoverEnv** - Drone control
6. **FluidManipulationEnv** - Robot interacting with SPH fluid

**Examples:**
- `simple/examples/physics/genesis_reaching.spl` - Train reaching policy
- `simple/examples/physics/genesis_locomotion.spl` - Train Ant to walk
- `simple/examples/physics/genesis_fluid.spl` - Fluid simulation demo
- `simple/examples/physics/genesis_distributed.spl` - Multi-GPU training

**Success Criteria:**
- ✅ FrankaReachEnv: >90% success rate in <100 epochs
- ✅ AntLocomotionEnv: >2.0 m/s velocity
- ✅ 1024 Ant envs: >500K FPS (500 FPS per env)
- ✅ Curriculum learning improves sample efficiency by 2x

---

## Build System Changes

### Cargo.toml Updates

**`src/runtime/Cargo.toml`:**
```toml
[features]
default = []
torch = ["tch"]
genesis = ["pyo3", "numpy", "torch"]  # Genesis requires torch for DLPack

[dependencies]
# PyTorch integration
tch = { version = "0.16", optional = true }

# Python integration (for Genesis)
pyo3 = { version = "0.20", features = ["auto-initialize", "abi3-py39"], optional = true }
numpy = { version = "0.20", optional = true }

# Existing dependencies
parking_lot = "0.12"
lazy_static = "1.4"
```

**Build Commands:**
```bash
# Phase I: PyTorch only
cargo build --features torch

# Phase II: Genesis (includes PyTorch)
cargo build --features genesis
```

---

## Testing Strategy

### Unit Tests (Per FFI Function)
- Test each `rt_torch_*` and `rt_genesis_*` function in isolation
- Verify value conversion (Simple ↔ C++ ↔ Python)
- Memory leak tests (Valgrind, 10K allocations)

### Integration Tests (Per Phase)
- Phase I Week 4: Tensor creation, matmul, GPU transfer
- Phase I Week 14: MNIST training to >95% accuracy
- Phase II Week 26: Scene creation, entity addition, simulation
- Phase II Week 37: Train reaching policy to >90% success

### System Tests (End-to-End)
- Train ResNet-18 on ImageNet (PyTorch)
- Train PPO policy on Ant locomotion (Genesis + PyTorch)
- Benchmark: 16K environments at 1M+ FPS

### Performance Benchmarks
- **PyTorch:** Within 5% of Python PyTorch training time
- **Genesis:** Within 10% of Genesis Python performance
- **DLPack:** Zero-copy verified (memory profiling)
- **Multi-GPU:** 1.8x speedup for 2 GPUs, 3.5x for 4 GPUs

---

## Success Metrics

### Phase I Success (Week 20)
- ✅ All 5 examples run successfully (MNIST, CIFAR-10, LSTM, VAE, DQN)
- ✅ MNIST MLP trains to >95% accuracy in <100 epochs
- ✅ Training performance within 5% of Python PyTorch
- ✅ Documentation covers 90% of API
- ✅ Zero memory leaks (Valgrind clean)

### Phase II Success (Week 37)
- ✅ FrankaReachEnv: 90% success in <100 epochs
- ✅ AntLocomotionEnv: 2.0+ m/s velocity
- ✅ 16K parallel envs at 1M+ FPS
- ✅ GPU memory <8GB for 1024 envs
- ✅ Type-safe units prevent dimensional errors
- ✅ Differentiable physics: gradients flow through simulation

### Overall Goals
- **Performance:** Match or exceed Python equivalents (<10% overhead)
- **Safety:** Type-safe units, no segfaults, graceful error handling
- **Scalability:** Linear scaling up to 16K envs on 4 GPUs
- **Documentation:** Comprehensive examples, API docs, migration guides

---

## Risk Mitigation

### Risk 1: LibTorch ABI Instability
**Impact:** High - Breaking changes between versions
**Mitigation:** Pin LibTorch version, use stable ABI, test upgrades in CI

### Risk 2: GIL Contention (Genesis)
**Impact:** High - Could limit parallelism
**Mitigation:** Multi-processing (not threading), batch operations, Genesis releases GIL during GPU compute

### Risk 3: DLPack Memory Corruption
**Impact:** Critical - Silent data corruption or crashes
**Mitigation:** Extensive testing with Valgrind/ASAN, reference counting, explicit lifetime management

### Risk 4: Performance Regression
**Impact:** High - FFI overhead could negate benefits
**Mitigation:** Zero-copy tensor sharing, benchmark each phase, abort if >20% overhead

### Risk 5: Genesis API Changes
**Impact:** Medium - Rapid evolution (0.3.3 → 0.4.x)
**Mitigation:** Pin Genesis version, abstract behind trait, monitor GitHub, plan migration

---

## Dependencies & Setup

### External Dependencies

**Phase I (PyTorch):**
```bash
# Download LibTorch (CPU + CUDA)
wget https://download.pytorch.org/libtorch/cu121/libtorch-cxx11-abi-shared-with-deps-2.5.0%2Bcu121.zip
unzip libtorch-*.zip -d /opt/libtorch

# Set environment
export LIBTORCH=/opt/libtorch
export LD_LIBRARY_PATH=$LIBTORCH/lib:$LD_LIBRARY_PATH
```

**Phase II (Genesis):**
```bash
# Python environment
python -m venv .venv
source .venv/bin/activate

# Install Genesis
pip install genesis-world>=0.3.3

# Set environment
export GENESIS_PYTHON_PATH=$(which python)
export PYTHONPATH=/path/to/genesis/install
```

### Feature Flags
```bash
# PyTorch only
cargo build --features torch

# Genesis (includes PyTorch via dependency)
cargo build --features genesis

# All features (for production)
cargo build --features torch,genesis,vulkan
```

---

## Integration with Existing Systems

### PyTorch ↔ Vulkan GPU
- DLPack for zero-copy tensor ↔ buffer conversion
- Shared GPU memory (no CPU round-trip)
- Custom SPIR-V kernels callable from PyTorch

### Genesis ↔ PyTorch
- Observations/actions are PyTorch tensors
- Zero-copy via DLPack (Genesis uses NumPy → DLPack → PyTorch)
- Policy networks consume Genesis tensors directly

### Actor System ↔ Distributed Training
- Each GPU worker is an actor
- Message-passing for gradient synchronization
- No GIL contention (multi-process actors)

### Unit System ↔ Physics
- All Genesis forces/torques use typed units
- Compile-time dimensional analysis
- Runtime validation via contracts

---

## Documentation Plan

### API Documentation
- Rustdoc for all FFI functions
- Simple docstrings with `#[doctest]` examples
- Type signatures with unit annotations

### User Guides
- `/doc/guides/pytorch_ml_framework.md` - ML framework guide
- `/doc/guides/genesis_physics.md` - Physics simulation guide
- `/doc/guides/distributed_training.md` - Multi-GPU training
- `/doc/guides/units_and_safety.md` - Type-safe units

### Example Suite
- 5+ PyTorch examples (`simple/examples/ml/`)
- 5+ Genesis examples (`simple/examples/physics/`)
- 2+ combined examples (RL policies trained in Genesis)

### Migration Guides
- Python PyTorch → Simple ML API mapping
- Genesis Python → Simple Physics API mapping
- Performance comparison tables

---

## Next Steps (Immediate)

### Week 1 Kickoff (Phase I Start)
1. Download LibTorch binaries (CPU + CUDA)
2. Create `src/runtime/src/value/torch.rs` skeleton
3. Create `src/runtime/src/value/torch_ffi_wrapper.cpp` skeleton
4. Update `src/runtime/Cargo.toml` with torch feature
5. Write smoke test: create tensor, free it
6. Verify build: `cargo build --features torch`

**First Milestone (Week 1 Day 5):**
```simple
// This should work by end of Week 1
import ml.torch

fn test_smoke():
    let t = Tensor::zeros([10, 10])
    println("Created tensor with shape: ${t.shape()}")
    // No crashes, no leaks
```

---

## Summary

This 37-week plan provides a complete roadmap to world-class ML and physics capabilities in Simple language:

**Phase I (20 weeks):** Full PyTorch ML framework - competitive with Python PyTorch
**Phase II (17 weeks):** Genesis physics engine - type-safe, actor-distributed, differentiable

**Key Innovations:**
- Type-safe units prevent physics errors (Force ≠ Torque)
- Actor-based distribution achieves 1M+ FPS (16K envs)
- Zero-copy DLPack integration (no performance penalty)
- Differentiable physics (gradients flow through simulation)

**Foundation Leveraged:**
- Vulkan GPU backend (handle-based pattern proven)
- FFI infrastructure (150+ functions, mature patterns)
- Actor system (message-passing concurrency)
- Effect system (`@async` for async physics)

**End Result:** Simple language becomes a premier choice for:
- Deep learning research and production
- Robotics simulation and training
- Embodied AI and reinforcement learning
- Differentiable physics and co-design
