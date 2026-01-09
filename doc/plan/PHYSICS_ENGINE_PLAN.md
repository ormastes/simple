# Physics Engine Integration Implementation Plan

**Created:** 2025-12-26
**Status:** Planning
**Priority:** High
**Target Engines:** Isaac Lab/Gym → Genesis

## Overview

Implement Simple language bindings for physics simulation engines focused on robotics and reinforcement learning. Start with Isaac Lab (more mature, NVIDIA support), then add Genesis for multi-physics capabilities. Leverage Simple's unique features (GPU/SIMD, unit types, actors, effects) for better performance and safety.

## Goals

1. Enable robot simulation and RL research in Simple
2. Provide type-safe physics APIs with dimensional analysis
3. Support GPU-accelerated batched simulation (1000s of parallel environments)
4. Leverage Simple actors for distributed simulation
5. Create common abstraction for multiple physics engines

## Phase 1: Isaac Lab Integration (4 months)

### Month 1: Python Bridge Foundation

**Week 1-2: CPython Embedding**
- [ ] Implement CPython embedding in Simple runtime
- [ ] Create Python GIL management
- [ ] Basic Python function calling from Simple
- [ ] Exception handling and error propagation

**Week 3-4: Type Marshalling**
- [ ] Simple ↔ Python type conversion
- [ ] NumPy array support
- [ ] PyTorch tensor marshalling
- [ ] DLPack zero-copy implementation

**Deliverable:** `simple.python` module for Python interop

### Month 2: Isaac Lab Core API

**Week 1-2: Environment Creation**
- [ ] Wrap `ManagerBasedRLEnv` class
- [ ] Configuration system (env configs)
- [ ] Scene setup and initialization
- [ ] Reset and step functions

**Week 3-4: Observation & Action Spaces**
- [ ] Tensor-based observations
- [ ] Action application
- [ ] Reward computation
- [ ] Episode termination handling

**Deliverable:** Simple can create and step Isaac Lab environments

### Month 3: Tensor Integration

**Week 1-2: DLPack Zero-Copy**
- [ ] Export Simple tensors to DLPack
- [ ] Import PyTorch tensors to Simple
- [ ] GPU memory sharing validation
- [ ] Performance benchmarking

**Week 3-4: Batched Operations**
- [ ] Batched environment stepping
- [ ] Parallel observation collection
- [ ] Vectorized action application
- [ ] GPU kernel profiling

**Deliverable:** Zero-copy tensor operations with 1000+ parallel envs

### Month 4: Sensors & Example

**Week 1-2: Sensor System**
- [ ] Camera sensors (RGB, depth, segmentation)
- [ ] Contact sensors
- [ ] Ray casters (LiDAR simulation)
- [ ] Joint state sensors

**Week 3-4: Example Environment**
- [ ] Implement CartPole environment in Simple
- [ ] Training loop with PPO
- [ ] Tensorboard logging
- [ ] Performance comparison vs Python

**Deliverable:** Complete RL training example in Simple

## Phase 2: Direct PhysX Bindings (2 months)

### Month 5: PhysX FFI

**Week 1-2: PhysX C++ API**
- [ ] Link to PhysX shared libraries
- [ ] FFI bindings for core types
- [ ] Scene creation and simulation
- [ ] Rigid body dynamics

**Week 3-4: CUDA Integration**
- [ ] Direct CUDA kernel access
- [ ] GPU memory management
- [ ] Tensor buffer sharing
- [ ] Performance optimization

**Deliverable:** Direct PhysX simulation from Simple (no Python overhead)

### Month 6: Performance Optimization

**Week 1-2: Benchmarking**
- [ ] Compare with Isaac Lab Python
- [ ] Profile FFI overhead
- [ ] Optimize hot paths
- [ ] Memory allocation profiling

**Week 3-4: Advanced Features**
- [ ] Articulation support (robot joints)
- [ ] Collision detection customization
- [ ] Contact callbacks
- [ ] Force/torque sensors

**Deliverable:** PhysX performance within 5% of native C++

## Phase 3: Genesis Integration (3 months)

### Month 7: Taichi Bridge

**Week 1-2: Taichi Integration**
- [ ] Understand Taichi Python API
- [ ] FFI to Taichi C++ API (if available)
- [ ] Or: Use Python bridge for Taichi
- [ ] Kernel compilation and execution

**Week 3-4: Genesis Scene API**
- [ ] Scene creation and configuration
- [ ] Solver selection (rigid, MPM, SPH, FEM)
- [ ] Material system
- [ ] Entity management

**Deliverable:** Simple can create Genesis scenes and run basic simulations

### Month 8: Multi-Solver Support

**Week 1-2: Rigid Body Solver**
- [ ] Rigid body dynamics (similar to PhysX)
- [ ] URDF loading
- [ ] Joint control
- [ ] Collision handling

**Week 3-4: Soft Body Solver (MPM)**
- [ ] MPM particle system
- [ ] Soft material properties
- [ ] Rigid-soft coupling
- [ ] Performance testing

**Deliverable:** Genesis rigid and MPM solvers working from Simple

### Month 9: Fluid Simulation & Example

**Week 1-2: SPH Fluid Solver**
- [ ] Fluid particle creation
- [ ] Viscosity and surface tension
- [ ] Fluid-rigid interaction
- [ ] Rendering/visualization

**Week 3-4: Example: Soft Robotics**
- [ ] Soft gripper simulation
- [ ] Deformable object manipulation
- [ ] Force sensing and control
- [ ] Documentation and tutorial

**Deliverable:** Unique soft robotics example showcasing Genesis capabilities

## Phase 4: Common Interface & Tools (2 months)

### Month 10: Unified API

**Week 1-2: Core Abstractions**
- [ ] Design `PhysicsWorld` trait
- [ ] Design `RigidBody` and `Articulation` traits
- [ ] Design `Sensor` trait hierarchy
- [ ] Design `Material` abstraction

**Week 3-4: Refactoring**
- [ ] Refactor Isaac implementation to use common traits
- [ ] Refactor Genesis implementation to use common traits
- [ ] Engine-agnostic examples
- [ ] Migration guide

**Deliverable:** `simple/std_lib/src/physics/` common interface module

### Month 11: Tooling & Documentation

**Week 1-2: Visualization**
- [ ] Real-time 3D viewer (using Simple's UI framework)
- [ ] Trajectory visualization
- [ ] Sensor data display
- [ ] Performance profiler

**Week 3-4: Documentation & Release**
- [ ] Complete API reference
- [ ] Getting started guides
- [ ] Tutorial series (basics → advanced RL)
- [ ] Example projects repository
- [ ] Package release

**Deliverable:** Public release of Simple physics engine support

## Technical Architecture

### Module Structure

```
simple/std_lib/src/
├── physics/              # Common interface
│   ├── __init__.spl
│   ├── world.spl         # PhysicsWorld trait
│   ├── body.spl          # RigidBody, Articulation traits
│   ├── sensor.spl        # Sensor trait hierarchy
│   ├── material.spl      # Material system
│   └── types.spl         # Common types (Transform, Force, etc.)
│
├── isaac/                # Isaac Lab/PhysX
│   ├── __init__.spl
│   ├── env.spl           # Environment wrapper
│   ├── physx.spl         # Direct PhysX bindings
│   ├── sensors.spl       # Sensor implementations
│   └── articulation.spl  # Robot control
│
├── genesis/              # Genesis multi-physics
│   ├── __init__.spl
│   ├── scene.spl         # Scene management
│   ├── solvers/          # Solver-specific APIs
│   │   ├── rigid.spl
│   │   ├── mpm.spl
│   │   ├── sph.spl
│   │   └── fem.spl
│   └── materials.spl     # Material definitions
│
└── python/               # Python interop (shared)
    ├── __init__.spl
    ├── embed.spl         # CPython embedding
    ├── types.spl         # Type conversion
    └── dlpack.spl        # Zero-copy tensors
```

### Type-Safe Physics with Units

```simple
# Leverage Simple's unit system
import simple.physics.isaac as isaac

# Create environment with type-safe forces
let env = isaac.make_env("Humanoid-v0", num_envs: 1024)

# Apply forces with dimensional checking
fn apply_control_force(robot: Articulation, target_vel: #Velocity):
    current_vel = robot.get_joint_velocities()  # Type: Array<#AngularVelocity>
    error = target_vel - current_vel

    # PD controller with proper units
    let kp: #Torque_per_Radian = 100.0#Nmrad
    let kd: #Torque_per_RadianPerSecond = 10.0#Nmradps

    let torque: #Torque = kp * error + kd * error.derivative()

    robot.apply_joint_torques(torque)  # Type-safe!
```

### Actor Model for Parallel Simulation

```simple
# Each environment is an actor - true parallelism
actor SimulationWorker:
    world: PhysicsWorld
    env_id: Int32

    async fn run_episode() -> EpisodeStats:
        obs = world.reset()
        total_reward = 0.0

        for step in 0..max_steps:
            action = policy(obs)

            # Each worker simulates independently
            obs, reward, done = world.step(action)
            total_reward += reward

            if done:
                break

        return EpisodeStats { total_reward, steps: step }

# Spawn 1024 workers (one per env)
let workers = (0..1024).map(|i| SimulationWorker.spawn(env_id: i))

# Run all episodes in parallel
let futures = workers.map(|w| w.run_episode())
let stats = await futures  # All workers run concurrently
```

### DLPack Zero-Copy

```simple
# Simple tensor
let simple_observations = Tensor<Float32>::new([4096, 37])

# Export to DLPack
let dlpack = simple_observations.to_dlpack()

# Use in Python/PyTorch (zero-copy!)
py.with_gil(|py_ctx| {
    torch = py_ctx.import("torch")
    torch_obs = torch.from_dlpack(dlpack)

    # Run neural network in PyTorch
    actions = policy_net.forward(torch_obs)

    # Import actions back (zero-copy!)
    actions_dlpack = actions.to_dlpack()
    simple_actions = Tensor::from_dlpack(actions_dlpack)
})

# Apply actions (all on GPU, no CPU transfer!)
env.step(simple_actions)
```

## Dependencies

### External Libraries
- **Isaac Lab:** Install via pip (`pip install isaaclab-rl`)
- **PhysX:** NVIDIA PhysX SDK 5.x (C++ libraries)
- **Genesis:** Install via pip (`pip install genesis-sim`)
- **Taichi:** Install via pip (`pip install taichi`)
- **CPython:** Python 3.10+ development headers
- **PyTorch:** LibTorch for DLPack support

### Simple Compiler Features Required
- ✅ FFI support
- ✅ GPU/CUDA integration
- ✅ Unit types (for physics quantities)
- ✅ Actor system (for parallel simulation)
- ✅ Effect system (for async safety)
- ⏳ Python interop (new, to be implemented)

## Success Metrics

### Performance
- [ ] 1000+ parallel environments on single GPU (RTX 4090)
- [ ] Performance within 5% of native Isaac Lab (Python)
- [ ] PhysX direct bindings faster than Isaac Lab
- [ ] Zero-copy tensor operations working

### Usability
- [ ] Developer can create RL environment in < 30 minutes
- [ ] Type system catches physics bugs at compile-time
- [ ] Clear error messages for dimension mismatches

### Safety
- [ ] Unit type checking prevents nonsensical operations
- [ ] GPU memory managed safely
- [ ] No segfaults from Python interop

### Research Impact
- [ ] Published RL results using Simple
- [ ] Community adoption in robotics research
- [ ] Faster experiment iteration vs Python

## Risks & Mitigations

### Risk: Python Overhead
**Mitigation:** Implement direct PhysX bindings, use DLPack for zero-copy, batch operations

### Risk: Complex Tensor Management
**Mitigation:** Clear ownership model, automatic GPU memory management, extensive testing

### Risk: Genesis Taichi Dependency
**Mitigation:** Start with Python bridge, investigate Taichi C++ API, consider pure-Simple fallback

### Risk: Limited Pretrained Models
**Mitigation:** Ensure PyTorch integration works seamlessly, provide model conversion tools

## Future Enhancements (Post-Release)

- [ ] Additional engines (MuJoCo, Bullet, custom Simple physics)
- [ ] Differentiable physics for gradient-based optimization
- [ ] Multi-GPU distributed simulation
- [ ] Real-time visualization in Simple UI framework
- [ ] Integration with Simple game engine support (Godot/Unreal)
- [ ] Sim-to-real transfer tools
- [ ] Hardware-in-the-loop simulation
- [ ] Cloud-based training infrastructure

## Example Applications

### 1. Robot Manipulation
```simple
import simple.physics.isaac as isaac

# Create environment
let env = isaac.make_env("FrankaPanda-v0", num_envs: 2048)

# Training loop
for episode in 0..10000:
    obs = env.reset()

    for step in 0..100:
        actions = policy(obs)
        obs, rewards, dones = env.step(actions)

        # Update policy
        loss = compute_loss(obs, actions, rewards)
        optimizer.step(loss)
```

### 2. Soft Robotics (Genesis)
```simple
import simple.physics.genesis as genesis

# Create scene with MPM
let scene = genesis.Scene(
    mpm_options: genesis.MPMOptions { ... }
)

# Soft gripper
let gripper = scene.add_soft_body(
    material: genesis.materials.Silicone(
        youngs_modulus: 1e6#Pa,
        poissons_ratio: 0.4
    ),
    mesh: "gripper.obj"
)

# Deformable object
let object = scene.add_mpm_entity(
    material: genesis.materials.Foam(...),
    particles: 10000
)

# Simulation
for step in 0..1000:
    gripper.set_actuator_positions(control_signal)
    scene.step(dt: 0.01#s)

    forces = gripper.get_contact_forces()
    print(f"Grip force: {forces.magnitude()}")
```

### 3. Legged Locomotion
```simple
import simple.physics.isaac as isaac

# Quadruped robot
let env = isaac.make_env("Anymal-v0", num_envs: 4096)

# Imitation learning from dataset
let dataset = load_motion_capture_data("dog_walk.npz")

for batch in dataset.batches(batch_size: 256):
    # Forward simulation
    predicted_poses = policy(batch.observations)

    # Compute imitation loss
    loss = (predicted_poses - batch.expert_poses).pow(2).mean()

    # Update policy
    optimizer.zero_grad()
    loss.backward()
    optimizer.step()
```

## References

- Research: `doc/research/physics_engine_integration.md`
- Isaac Lab Docs: https://isaac-sim.github.io/IsaacLab/
- Genesis Docs: https://genesis-world.readthedocs.io/
- PhysX SDK: https://developer.nvidia.com/physx-sdk
- DLPack Spec: https://github.com/dmlc/dlpack
