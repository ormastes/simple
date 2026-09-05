# Physics Simulation Engine Integration Research

**Date:** 2025-12-26
**Status:** Research Complete
**Target Engines:** Genesis (v0.3.3+), Isaac Lab/Gym (NVIDIA)

## Executive Summary

This document outlines research for integrating Simple language with modern physics simulation engines focused on robotics and reinforcement learning. The goal is to provide high-performance, GPU-accelerated physics simulation with type-safe APIs and Simple's unique features.

**Key Findings:**
- Both engines provide Python APIs; C++/CUDA backends accessible via FFI
- Common abstractions possible: worlds, rigid bodies, sensors, actions
- GPU batching critical for RL performance (1000s of parallel envs)
- Isaac Lab should be implemented first (more mature, NVIDIA support)

---

## 1. Genesis Physics Engine (v0.3.3+)

### 1.1 Architecture Overview

**What is Genesis?**
- Universal physics engine for robotics and beyond
- Multiple backends: Rigid, MPM, SPH, FEM, PBD, Stable Fluid
- GPU-accelerated via Taichi (Python→CUDA/Vulkan)
- Unified API across different physics solvers

**Core Philosophy:**
> "Genesis is designed to be a universal physics engine that can handle various simulation scenarios from rigid body dynamics to soft body simulation and fluid dynamics."

### 1.2 Physics Solvers

**Rigid Body Dynamics:**
```python
# Genesis Python API - reference for Simple
import genesis as gs

scene = gs.Scene(
    sim_options=gs.options.SimOptions(
        dt=0.01,
        gravity=(0, 0, -9.81),
    ),
    rigid_options=gs.options.RigidOptions(
        enable_joint_limit=True,
        enable_collision=True,
    ),
)

# Add entities
robot = scene.add_entity(gs.morphs.URDF(file="robot.urdf"))
```

**Material Point Method (MPM) - Soft Bodies:**
- Simulates deformable materials
- Snow, sand, mud, soft tissues
- GPU-parallelized particle updates

**Smoothed Particle Hydrodynamics (SPH) - Fluids:**
- Particle-based fluid simulation
- Water, viscous fluids
- Efficient neighbor search on GPU

**Finite Element Method (FEM):**
- Detailed deformable body simulation
- High-quality soft body physics

**Position-Based Dynamics (PBD):**
- Fast, stable constraint-based physics
- Good for real-time robotics

### 1.3 API Surface

**Scene Management:**
```python
# Python - Simple would mirror structure
scene = gs.Scene()
scene.build()  # Finalize scene graph

# Simulation loop
for i in range(1000):
    scene.step()  # Advance physics
    state = scene.get_state()  # Get observations
```

**Entity Creation:**
```python
# Primitives
box = scene.add_entity(gs.morphs.Box(size=(1, 1, 1)))
sphere = scene.add_entity(gs.morphs.Sphere(radius=0.5))

# From files
robot = scene.add_entity(gs.morphs.URDF(file="robot.urdf"))
mesh = scene.add_entity(gs.morphs.Mesh(file="object.obj"))

# Soft bodies (MPM)
snow = scene.add_entity(gs.morphs.MPM(
    material=gs.materials.Snow(),
    particle_count=10000,
))
```

**Materials & Properties:**
```python
# Rigid body material
material = gs.materials.Rigid(
    density=1000.0,        # kg/m³
    friction=0.5,          # μ
    restitution=0.3,       # coefficient of restitution
)

# MPM material (soft body)
mpm_material = gs.materials.MPM(
    youngs_modulus=1e5,    # Pa
    poissons_ratio=0.3,
)
```

### 1.4 GPU Acceleration

**Taichi Backend:**
- JIT compiles Python to CUDA/Vulkan kernels
- Automatic parallelization
- Supports both CUDA and Vulkan

**Performance Characteristics:**
- 1000s of parallel rigid body simulations on single GPU
- MPM: 1M+ particles at interactive rates
- SPH: 100K+ fluid particles

**Batching:**
```python
# Parallel environments for RL
scenes = [gs.Scene() for _ in range(1024)]

# Batch step on GPU
states = gs.batch_step(scenes)  # All scenes step in parallel
```

### 1.5 Observation & Action Spaces

**Sensors:**
```python
# Joint state
joint_positions = robot.get_joint_positions()
joint_velocities = robot.get_joint_velocities()

# Camera/LiDAR
camera = scene.add_camera(
    pos=(0, -2, 1),
    lookat=(0, 0, 0.5),
    res=(640, 480),
)
image = camera.render()  # RGB-D on GPU

lidar = scene.add_lidar(
    pos=(0, 0, 1),
    num_rays=360,
)
scan = lidar.get_scan()
```

**Actions:**
```python
# Joint control
robot.set_joint_torques([1.0, 0.5, -0.3, ...])
robot.set_joint_positions([0.1, 0.2, 0.3, ...])
robot.set_joint_velocities([0.5, 0.0, 0.5, ...])
```

### 1.6 Integration Points

**C++ API (if available):**
- Taichi provides C++ backend
- Can FFI directly to CUDA kernels
- Bypasses Python interpreter

**Python Interop:**
- Embed Python via CPython C API
- Call Genesis from Simple
- Marshal tensors zero-copy

---

## 2. Isaac Lab / Isaac Gym (NVIDIA)

### 2.1 Architecture Overview

**Isaac Lab:**
- Built on Isaac Sim (NVIDIA Omniverse)
- Uses PhysX 5 for physics
- GPU-accelerated via CUDA
- RL-focused API (Gym/Gymnasium compatible)
- Replaced Isaac Gym (deprecated)

**Isaac Gym (legacy, but reference):**
- Standalone GPU physics simulator
- Direct PhysX on CUDA
- Extremely fast (10K+ envs on single GPU)
- Tensor-based API

### 2.2 Core Concepts

**Environments:**
```python
# Isaac Lab API
import isaaclab

env_cfg = isaaclab.envs.ManagerBasedRLEnvConfig(
    scene=SceneConfig(...),
    observations=ObservationConfig(...),
    actions=ActionConfig(...),
    rewards=RewardConfig(...),
)

env = isaaclab.envs.ManagerBasedRLEnv(env_cfg)
env.reset()

for _ in range(1000):
    actions = policy(obs)
    obs, rewards, dones, info = env.step(actions)
```

**Batched Simulation:**
```python
# 4096 parallel environments
env = isaaclab.envs.create_env(
    "CartPole-v0",
    num_envs=4096,
    device="cuda:0",
)

# All envs step in parallel on GPU
obs = env.reset()  # Shape: (4096, obs_dim)
actions = torch.randn(4096, action_dim, device="cuda:0")
obs, rewards, dones, info = env.step(actions)
```

### 2.3 PhysX Integration

**PhysX 5 Features:**
- GPU-accelerated rigid body dynamics
- Articulations (robot joints)
- Collision detection (broad + narrow phase)
- Particle systems
- Tensors directly on GPU

**Articulation API:**
```python
# Robot articulation
articulation = ArticulationView(
    prim_paths_expr="/World/Robot.*",
    name="robot_view",
)

# Get/set states (tensors on GPU)
joint_positions = articulation.get_joint_positions()  # (N, DOF) on CUDA
joint_velocities = articulation.get_joint_velocities()

# Apply actions
articulation.set_joint_position_targets(targets)
articulation.set_joint_velocity_targets(targets)
articulation.set_joint_efforts(torques)
```

### 2.4 Sensor System

**Cameras:**
```python
camera = Camera(
    prim_path="/World/Camera",
    resolution=(640, 480),
    position=(2.0, 2.0, 2.0),
)

# Render (GPU)
rgb = camera.get_rgb()      # (H, W, 3) on CUDA
depth = camera.get_depth()  # (H, W, 1) on CUDA
```

**Contact Sensors:**
```python
contact_sensor = ContactSensor(
    prim_path="/World/Robot/gripper",
)

# Get contact forces (GPU tensors)
forces = contact_sensor.get_net_contact_forces()  # (N, 3)
```

**Ray Casters:**
```python
ray_caster = RayCaster(
    prim_path="/World/Sensors",
    num_rays=360,
)

distances = ray_caster.get_distances()  # (N, 360) on CUDA
```

### 2.5 USD (Universal Scene Description)

**Scene Representation:**
- Isaac uses USD for scene graphs
- Hierarchical composition
- Variantsets for different configs
- Python API + C++ USD library

```python
# USD scene building
from pxr import Usd, UsdGeom, UsdPhysics

stage = Usd.Stage.CreateNew("scene.usd")
xform = UsdGeom.Xform.Define(stage, "/World")

# Add physics
prim = stage.GetPrimAtPath("/World/Box")
UsdPhysics.RigidBodyAPI.Apply(prim)
UsdPhysics.CollisionAPI.Apply(prim)
```

### 2.6 GPU Memory Management

**Tensor Interface:**
```python
# All tensors are PyTorch on CUDA
import torch

# Observations
obs = env.reset()  # torch.Tensor on cuda:0
assert obs.device == torch.device("cuda:0")

# Zero-copy access to PhysX buffers
positions = articulation.get_world_positions()  # Direct GPU buffer
```

**Memory Layout:**
- Structure-of-Arrays (SoA) for cache efficiency
- Coalesced memory access
- Minimal CPU↔GPU transfers

---

## 3. Common Interface Design

### 3.1 Core Abstractions

**World/Scene:**
```simple
trait PhysicsWorld:
    fn add_rigid_body(desc: RigidBodyDesc) -> RigidBodyHandle
    fn add_articulation(urdf_path: String) -> ArticulationHandle
    fn step(dt: #Duration)
    fn reset()
    fn get_state() -> WorldState

# Genesis implementation
class GenesisWorld(PhysicsWorld):
    native: GenesisScene
    # ...

# Isaac implementation
class IsaacWorld(PhysicsWorld):
    native: IsaacEnv
    # ...
```

**Rigid Body:**
```simple
struct RigidBodyDesc:
    shape: CollisionShape
    mass: #Mass
    friction: Float32
    restitution: Float32
    initial_pose: Transform3D

enum CollisionShape:
    Box(size: Vector3)
    Sphere(radius: Float32)
    Capsule(radius: Float32, height: Float32)
    Mesh(vertices: Array<Vector3>, indices: Array<Int32>)

trait RigidBody:
    fn get_position() -> Vector3
    fn get_velocity() -> #Velocity
    fn set_position(pos: Vector3)
    fn apply_force(force: #Force)
    fn apply_torque(torque: #Torque)
```

**Articulation (Robot):**
```simple
struct ArticulationDesc:
    urdf_path: String
    base_pose: Transform3D

trait Articulation:
    fn get_dof() -> Int32
    fn get_joint_positions() -> Array<Float32>
    fn get_joint_velocities() -> Array<#AngularVelocity>
    fn set_joint_targets(targets: Array<Float32>)
    fn set_joint_torques(torques: Array<#Torque>)
```

### 3.2 Batched Environments (for RL)

**Parallel Simulation:**
```simple
# Common batched env interface
class BatchedEnv:
    num_envs: Int32
    worlds: Array<PhysicsWorld>

    fn reset() -> Tensor<Float32>:  # (num_envs, obs_dim)
        # Reset all envs in parallel (GPU)
        pass

    fn step(actions: Tensor<Float32>) -> StepResult:
        # actions: (num_envs, action_dim)
        # returns: obs, rewards, dones, info
        pass

struct StepResult:
    observations: Tensor<Float32>  # (num_envs, obs_dim)
    rewards: Tensor<Float32>       # (num_envs,)
    dones: Tensor<Bool>            # (num_envs,)
    info: Dict<String, Tensor>
```

### 3.3 Sensor Abstraction

**Camera:**
```simple
trait Camera:
    fn get_resolution() -> (Int32, Int32)
    fn get_rgb() -> Tensor<UInt8>     # (H, W, 3)
    fn get_depth() -> Tensor<Float32> # (H, W)
    fn get_segmentation() -> Tensor<Int32>
    fn set_pose(pos: Vector3, lookat: Vector3)
```

**Contact Sensor:**
```simple
trait ContactSensor:
    fn get_contact_forces() -> Array<#Force>
    fn is_in_contact() -> Bool
    fn get_contact_points() -> Array<Vector3>
```

**Ray Caster (LiDAR):**
```simple
struct RayCasterConfig:
    num_rays: Int32
    max_distance: Float32
    horizontal_fov: Float32  # degrees

trait RayCaster:
    fn get_distances() -> Array<Float32>
    fn get_hit_positions() -> Array<Vector3>
    fn get_hit_normals() -> Array<Vector3>
```

### 3.4 Material System

**Unified Material Properties:**
```simple
struct RigidMaterial:
    density: #Density        # kg/m³
    friction: Float32        # 0..1
    restitution: Float32     # 0..1 (bounciness)

struct SoftMaterial:
    youngs_modulus: #Pressure   # Pa (stiffness)
    poissons_ratio: Float32     # 0..0.5
    damping: Float32

struct FluidMaterial:
    viscosity: #Viscosity    # Pa⋅s
    surface_tension: Float32
    density: #Density
```

---

## 4. Simple Language Unique Features

### 4.1 Unit Types for Physics

**Type-Safe Physical Quantities:**
```simple
# Simple's unit system is perfect for physics!

# Forces
let gravity: #Force = 9.81#N
let drag: #Force = -0.5 * velocity^2 * area * drag_coeff

# Torques
let motor_torque: #Torque = 10.0#Nm
robot.apply_joint_torque(joint_id, motor_torque)

# Velocities
let linear_vel: #Velocity = 2.5#mps  # meters/second
let angular_vel: #AngularVelocity = 1.57#radps  # rad/s

# Compile-time dimensional analysis
let force: #Force = 10.0#N
let mass: #Mass = 2.0#kg
let acceleration = force / mass  # Type: #Acceleration
robot.set_acceleration(acceleration)  # Type-safe!

# Prevents nonsensical operations
robot.apply_force(mass)  # ERROR: Expected #Force, got #Mass
```

**Benefits:**
- Catches physics bugs at compile-time
- Self-documenting code
- No runtime overhead (zero-cost)

### 4.2 GPU/SIMD Integration

**Direct CUDA Access:**
```simple
# Simple can call CUDA kernels directly
import simple.gpu.cuda

@[cuda_kernel]
fn update_particles(
    positions: mut Tensor<Vector3>,
    velocities: Tensor<Vector3>,
    forces: Tensor<#Force>,
    dt: #Duration,
    mass: #Mass
):
    tid = get_thread_id()
    acceleration = forces[tid] / mass
    velocities[tid] += acceleration * dt.to_seconds()
    positions[tid] += velocities[tid] * dt.to_seconds()

# Call from Simple
update_particles<<<num_blocks, threads_per_block>>>(
    positions, velocities, forces, dt, mass
)
```

**Vulkan Compute:**
```simple
# Alternative: Vulkan compute shaders
@[compute_shader(local_size_x=256)]
fn simulate_rigid_bodies(
    bodies: mut StructuredBuffer<RigidBody>,
    dt: #Duration
):
    let id = get_global_invocation_id()
    let body = bodies[id]

    # Integrate velocity
    body.velocity += body.force / body.mass * dt.to_seconds()
    body.position += body.velocity * dt.to_seconds()

    bodies[id] = body
```

### 4.3 Actor Model for Parallel Simulation

**Distributed Physics:**
```simple
# Each physics world is an actor
actor PhysicsWorker:
    world: PhysicsWorld
    env_id: Int32

    async fn reset() -> Observation:
        world.reset()
        return world.get_observation()

    async fn step(action: Action) -> (Observation, Float32, Bool):
        world.apply_action(action)
        world.step(dt: 0.01#s)

        obs = world.get_observation()
        reward = calculate_reward()
        done = check_termination()

        return (obs, reward, done)

# Spawn 1024 parallel workers
let workers = Array::new()
for i in 0..1024:
    worker = PhysicsWorker.spawn(env_id: i)
    workers.push(worker)

# Parallel step (true concurrency!)
let futures = workers.map(|w| w.step(actions[w.env_id]))
let results = await futures  # All workers run in parallel
```

**Advantages:**
- True multi-core physics simulation
- No manual thread management
- Type-safe message passing

### 4.4 Effect System for GPU Operations

**Safe Async Physics:**
```simple
# Mark GPU operations explicitly
@[effect(async, gpu)]
async fn simulate_batch(
    envs: mut Array<PhysicsWorld>,
    actions: Tensor<Float32>
):
    # Effect system ensures:
    # - GPU tensors not accessed from CPU code
    # - Async operations properly awaited
    # - No data races

    for i, env in envs.enumerate():
        env.apply_action(actions[i])

    # Batch step on GPU
    await gpu_batch_step(envs)

# Compiler prevents misuse
@[effect(sync)]
fn cpu_only_function():
    simulate_batch(...)  # ERROR: Can't call async from sync
```

### 4.5 Memory Safety for Simulation Data

**Reference Capabilities:**
```simple
# Immutable observation (can be safely shared)
struct Observation:
    joint_positions: Array<Float32>
    joint_velocities: Array<Float32>
    contact_forces: Array<#Force>

# Mutable world state (exclusive access)
class PhysicsWorld:
    bodies: mut Array<RigidBody>
    constraints: mut Array<Constraint>

    fn step(dt: #Duration):
        # mut access guaranteed exclusive
        for body in self.bodies:
            integrate(body, dt)

# Isolated transfer (move ownership)
fn create_world() -> iso PhysicsWorld:
    world = iso PhysicsWorld()
    # ... setup
    return world  # Transfer ownership
```

---

## 5. Implementation Strategy

### 5.1 Phase 1: Isaac Lab Integration (Months 1-4)

**Why Isaac First:**
- More mature than Genesis
- Better documentation
- NVIDIA support and ecosystem
- Proven at scale (industry standard)

**Milestones:**

**M1.1: Python Bridge (Month 1)**
- Embed CPython in Simple runtime
- Marshal Simple types ↔ Python types
- Call Isaac Lab from Simple
- Handle NumPy/PyTorch tensors

**M1.2: Core API Wrapping (Month 2)**
- Wrap `ManagerBasedRLEnv`
- Scene configuration
- Observation/Action spaces
- Reset/Step functions

**M1.3: Tensor Integration (Month 2-3)**
- Zero-copy Simple ↔ PyTorch
- DLPack tensor protocol
- GPU memory management
- Batched operations

**M1.4: Sensor Support (Month 3)**
- Camera (RGB/Depth)
- Contact sensors
- Ray casters
- Custom sensors

**M1.5: Example Environment (Month 4)**
- CartPole in Simple
- Humanoid robot control
- Demonstrates batching
- Training loop with PPO

### 5.2 Phase 2: Direct PhysX Bindings (Months 5-6)

**Bypass Python:**
- FFI to PhysX C++ API
- Direct CUDA kernel access
- Lower latency
- Better performance

**Components:**
```simple
# Direct PhysX API
import simple.physics.physx

let physics = PhysX::create(
    gpu_device_id: 0,
    num_threads: 8,
)

let scene = physics.create_scene(
    gravity: Vector3(0, 0, -9.81),
)

# Add actor
let actor_desc = RigidDynamicDesc {
    shape: Box(1.0, 1.0, 1.0),
    material: RigidMaterial {
        friction: 0.5,
        restitution: 0.3,
        density: 1000.0#kgpm3,
    },
}

let actor = scene.add_actor(actor_desc)
```

### 5.3 Phase 3: Genesis Integration (Months 7-9)

**Building on Common Interface:**

**M3.1: Taichi Bridge (Month 7)**
- Understand Taichi IR
- Generate Taichi kernels from Simple
- Or: FFI to Taichi C++ API

**M3.2: Multi-Solver Support (Month 8)**
- Rigid body (easy - similar to PhysX)
- MPM (soft bodies)
- SPH (fluids)
- Choose solver at runtime

**M3.3: Hybrid Simulation (Month 9)**
- Combine rigid + soft bodies
- Rigid robot in fluid environment
- Cloth simulation on robot

**M3.4: Example: Soft Robotics (Month 9)**
- Soft gripper simulation
- Demonstrates MPM/FEM
- Unique to Genesis

### 5.4 Phase 4: Common Interface Refinement (Month 10-11)

**Extract Common Patterns:**
1. Analyze Isaac + Genesis implementations
2. Design trait-based unified API
3. Refactor both to use common traits
4. Benchmark performance

**Deliverables:**
- `simple/std_lib/src/physics/` module
- Common world/body/sensor interfaces
- Engine-agnostic examples
- Migration guide

### 5.5 Python Interop Architecture

**CPython Embedding:**
```rust
// Rust FFI layer (in runtime)
use pyo3::prelude::*;

#[no_mangle]
pub extern "C" fn simple_python_init() {
    pyo3::prepare_freethreaded_python();
}

#[no_mangle]
pub extern "C" fn simple_python_call(
    module: *const c_char,
    function: *const c_char,
    args: *const SimpleValue,
    num_args: usize,
) -> SimpleValue {
    Python::with_gil(|py| {
        let module = PyModule::import(py, module)?;
        let func = module.getattr(function)?;
        // ...call and marshal result
    })
}
```

**Simple API:**
```simple
# High-level Simple API
import simple.python

let isaac_lab = python.import("isaaclab")

let env_class = isaac_lab.get_attr("envs").get_attr("ManagerBasedRLEnv")
let env = env_class.call(cfg: env_config)

# Step
let obs = env.call_method("reset")
let result = env.call_method("step", actions)
```

### 5.6 Zero-Copy Tensor Sharing

**DLPack Protocol:**
```simple
# Simple tensor to PyTorch (zero-copy)
let simple_tensor = Tensor<Float32>::new([4096, 10])

# Export as DLPack
let dlpack_capsule = simple_tensor.to_dlpack()

# Import in PyTorch
let torch_tensor = torch.from_dlpack(dlpack_capsule)

# Both tensors share same GPU memory!
assert simple_tensor.data_ptr() == torch_tensor.data_ptr()
```

**Benefits:**
- No copy overhead
- GPU → GPU direct
- Works with NumPy, PyTorch, JAX, etc.

---

## 6. Use Cases & Applications

### 6.1 Robot Learning

**Reinforcement Learning:**
```simple
import simple.physics.isaac as isaac
import simple.ml.torch as torch

# Create batched environment
let env = isaac.make_env("Humanoid-v0", num_envs: 4096)

# Training loop
let policy = torch.load("policy.pt")
let optimizer = torch.optim.Adam(policy.parameters())

for episode in 0..10000:
    obs = env.reset()

    for step in 0..1000:
        # Get actions from policy
        actions = policy.forward(obs)

        # Step all envs in parallel (GPU)
        obs, rewards, dones, info = env.step(actions)

        # Update policy
        loss = compute_ppo_loss(obs, actions, rewards)
        optimizer.zero_grad()
        loss.backward()
        optimizer.step()
```

### 6.2 Soft Robotics

**Gripper Simulation (Genesis MPM):**
```simple
import simple.physics.genesis as genesis

let scene = genesis.Scene(
    rigid_options: RigidOptions { ... },
    mpm_options: MPMOptions {
        particle_size: 0.001,
        grid_size: 0.01,
    },
)

# Rigid robot arm
let robot = scene.add_urdf("gripper.urdf")

# Soft object (MPM)
let soft_object = scene.add_mpm_entity(
    material: genesis.materials.Elastomer(
        youngs_modulus: 1e6#Pa,
        poissons_ratio: 0.4,
    ),
    particles: 10000,
    shape: Sphere(radius: 0.05),
)

# Simulation loop
for i in 0..1000:
    # Control gripper
    robot.set_joint_targets(gripper_open_close[i])

    # Step both rigid and soft physics
    scene.step(dt: 0.01#s)

    # Measure contact forces
    forces = soft_object.get_contact_forces()
    print(f"Contact force: {forces.magnitude()}")
```

### 6.3 Fluid-Structure Interaction

**Robot in Water (Genesis SPH):**
```simple
let scene = genesis.Scene(
    sph_options: SPHOptions {
        particle_radius: 0.01,
        smoothing_length: 0.02,
    },
)

# Underwater robot (rigid)
let robot = scene.add_urdf("underwater_robot.urdf")

# Water (SPH)
let water = scene.add_sph_entity(
    material: genesis.materials.Fluid(
        viscosity: 0.001#Pas,  # Water viscosity
        density: 1000.0#kgpm3,
    ),
    particles: 100000,
    bounds: Box(10.0, 10.0, 5.0),
)

# Simulation
for step in 0..10000:
    # Apply thruster forces
    robot.apply_force(Vector3(thrust_x, thrust_y, thrust_z))

    scene.step(dt: 0.01#s)

    # Get fluid drag forces on robot
    drag = water.get_force_on_body(robot)
```

### 6.4 Multi-Agent Robotics

**Swarm Simulation:**
```simple
# Leverage Simple's actor model for multi-agent
actor RobotAgent:
    robot_id: Int32
    world: PhysicsWorld

    async fn run_policy(obs: Observation) -> Action:
        # Each robot runs independently
        # Can have different policies
        action = self.compute_action(obs)
        return action

# Create swarm
let agents = Array::new()
for i in 0..100:
    agent = RobotAgent.spawn(
        robot_id: i,
        world: shared_world,  # All agents in same world
    )
    agents.push(agent)

# Decentralized control
loop:
    # Each agent observes independently
    let obs_futures = agents.map(|a| a.observe())
    let observations = await obs_futures

    # Each agent computes action in parallel
    let action_futures = agents.map(|a| a.run_policy(observations[a.robot_id]))
    let actions = await action_futures

    # Apply all actions and step
    shared_world.apply_actions(actions)
    shared_world.step(dt: 0.01#s)
```

---

## 7. Performance Considerations

### 7.1 Benchmarks (Reference)

**Isaac Lab (reported):**
- Humanoid (4096 envs): 150K+ FPS on RTX 4090
- Ant (8192 envs): 300K+ FPS
- CartPole (16384 envs): 1M+ FPS

**Genesis (reported):**
- Rigid bodies: 1M+ bodies on single GPU
- MPM particles: 10M+ particles at 20 FPS
- SPH fluids: 1M+ particles at 30 FPS

**Target (Simple):**
- Match native performance (within 5%)
- Minimize Python overhead
- Zero-copy tensor operations

### 7.2 Optimization Strategies

**Batching:**
```simple
# Batch all operations on GPU
fn batch_step(envs: Array<PhysicsWorld>, actions: Tensor<Float32>):
    # Single kernel launch for all envs
    gpu_batch_apply_actions(envs, actions)
    gpu_batch_integrate(envs, dt)
    gpu_batch_detect_collisions(envs)
    gpu_batch_solve_constraints(envs)
```

**Memory Layout:**
```simple
# Structure-of-Arrays (SoA) for cache efficiency
struct RigidBodySoA:
    positions: Array<Vector3>      # Contiguous
    velocities: Array<Vector3>     # Contiguous
    masses: Array<#Mass>           # Contiguous

# Better than Array-of-Structures (AoS)
# GPU can coalesce memory accesses
```

**Kernel Fusion:**
```simple
# Fuse multiple operations into single kernel
@[cuda_kernel(fused)]
fn integrate_and_detect_collisions(
    bodies: mut RigidBodySoA,
    dt: #Duration,
    broad_phase_grid: mut Grid,
):
    # Integrate
    update_velocities(bodies, dt)
    update_positions(bodies, dt)

    # Update spatial hash in same kernel
    update_grid(bodies, broad_phase_grid)
```

---

## 8. Challenges & Mitigations

### 8.1 Python Overhead

**Challenge:** Python interpreter adds latency
**Mitigations:**
- Direct C++/CUDA FFI (bypass Python)
- Batch operations to amortize overhead
- JIT compile Simple → CUDA for hot paths
- Use DLPack for zero-copy tensors

### 8.2 Tensor Type Compatibility

**Challenge:** PyTorch/NumPy tensors vs Simple tensors
**Mitigations:**
- Implement DLPack protocol
- Automatic conversion helpers
- Clear documentation on ownership
- Static type checking for tensor shapes

```simple
# Type-safe tensor shapes
type Observation = Tensor<Float32, shape: [num_envs, 37]>
type Action = Tensor<Float32, shape: [num_envs, 12]>

fn step(actions: Action) -> Observation:
    # Compiler checks shape compatibility
    pass
```

### 8.3 GPU Memory Management

**Challenge:** Who owns GPU memory? Simple or Python/C++?
**Mitigations:**
- Explicit ownership markers (iso/mut)
- Reference counting for shared tensors
- Clear API contracts
- Memory pools for allocations

### 8.4 Multi-Solver Integration (Genesis)

**Challenge:** Different solvers have different APIs
**Mitigations:**
- Unified trait interface
- Solver-specific extensions
- Runtime solver selection
- Clear migration path

### 8.5 Debugging

**Challenge:** GPU errors are hard to debug
**Mitigations:**
- CPU fallback mode for debugging
- Tensor bounds checking (debug builds)
- CUDA error checking helpers
- Integration with NVIDIA Nsight

---

## 9. Documentation & Examples

### 9.1 Getting Started Guide

**Isaac Lab:**
```markdown
# Getting Started with Isaac Lab in Simple

## 1. Install dependencies
$ pip install isaaclab-rl  # Isaac Lab
$ cargo install simple-lang  # Simple compiler

## 2. Create project
$ simple new --template physics-isaac my_robot_env

## 3. Define environment
# envs/cartpole.spl
import simple.physics.isaac

class CartPoleEnv:
    env: isaac.ManagerBasedRLEnv

    fn init():
        cfg = isaac.configs.CartPoleEnvCfg(num_envs: 1024)
        self.env = isaac.ManagerBasedRLEnv(cfg)

    fn reset() -> Observation:
        return self.env.reset()

    fn step(actions: Actions) -> StepResult:
        return self.env.step(actions)

## 4. Run training
$ simple run train.spl
```

### 9.2 Example Projects

1. **Robot Manipulation (Isaac Lab)**
   - Franka arm pick-and-place
   - Camera-based observation
   - 4096 parallel envs

2. **Soft Gripper (Genesis MPM)**
   - Deformable object grasping
   - MPM-rigid coupling
   - Force sensing

3. **Legged Locomotion (Isaac Lab)**
   - Quadruped robot
   - Terrain adaptation
   - Imitation learning

4. **Underwater ROV (Genesis SPH)**
   - Fluid dynamics
   - Thruster control
   - Buoyancy simulation

### 9.3 API Reference

**Auto-Generated Docs:**
```bash
$ simple doc --module physics
# Generates:
# - simple/std_lib/src/physics/README.md
# - HTML docs at docs/physics/index.html
```

---

## 10. Comparison with Alternatives

### 10.1 MuJoCo

**MuJoCo:**
- Industry standard for robotics
- Contact-rich simulation
- CPU-based (mostly)

**vs Simple:**
- Simple offers GPU batching (via Isaac/Genesis)
- Type-safe physics with units
- Actor model for parallel envs
- Better async story

### 10.2 PyBullet

**PyBullet:**
- Popular for RL research
- Python-only API
- CPU-based

**vs Simple:**
- Simple has native GPU support
- Compile-time safety
- Better performance (GPU batching)
- Actor model for scaling

### 10.3 Brax (Google)

**Brax:**
- JAX-based physics
- Fully differentiable
- GPU-accelerated

**vs Simple:**
- Brax is pure functional (JAX)
- Simple has imperative API (easier for roboticists)
- Simple has better type safety (units!)
- Both have good GPU support

---

## 11. Roadmap & Future Work

### 11.1 Advanced Features

**Differentiable Physics:**
- Automatic differentiation through physics
- For gradient-based optimization
- Leverage Simple's AD capabilities

```simple
@[differentiable]
fn simulate_trajectory(
    initial_state: State,
    controls: Array<Action>
) -> Trajectory:
    state = initial_state

    for action in controls:
        state = physics_step(state, action)

    return state.trajectory

# Get gradients
let grad_controls = backward(simulate_trajectory, loss)
```

**Mesh-Based Simulation:**
- Tetrahedral meshes for FEM
- Triangle meshes for collision
- Signed distance fields (SDF)

**Advanced Sensors:**
- Event cameras
- Tactile sensors
- IMU/Gyroscope

### 11.2 Tooling

**Visualization:**
- Real-time 3D viewer (using Simple's UI framework)
- Trajectory visualization
- Tensor inspection

**Profiling:**
- GPU kernel profiling
- Memory usage tracking
- Performance bottleneck detection

---

## 12. Conclusion & Recommendations

### Recommended Implementation Order:

1. **Phase 1: Isaac Lab Core (4 months)**
   - Python bridge
   - Core API wrapping
   - Tensor integration
   - CartPole example

2. **Phase 2: Direct PhysX (2 months)**
   - C++ FFI bindings
   - Performance optimization
   - Benchmarking

3. **Phase 3: Genesis Integration (3 months)**
   - Taichi bridge
   - Multi-solver support
   - Soft robotics examples

4. **Phase 4: Common Interface (2 months)**
   - Extract common patterns
   - Refactor implementations
   - Documentation

### Success Metrics:

- Performance within 5% of native
- Zero-copy tensor operations
- Type-safety for all physics operations
- 1000+ parallel envs on single GPU
- Developer productivity (lines of code, iteration time)

### Next Steps:

1. Prototype Python bridge (2 weeks)
2. Validate Isaac Lab integration (1 month)
3. Benchmark performance (ongoing)
4. Gather community feedback
5. Begin Phase 1 implementation
