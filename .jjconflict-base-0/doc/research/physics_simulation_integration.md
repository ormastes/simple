# Physics Simulation Engine Integration Research

**Author:** Research Team
**Date:** 2025-12-26
**Status:** Comprehensive Research
**Target:** Simple Language Integration Strategy

## Executive Summary

This document provides comprehensive research on integrating physics simulation engines (Genesis and Isaac Lab/Gym) with the Simple programming language. Both engines offer state-of-the-art GPU-accelerated physics simulation for robotics and embodied AI applications, with complementary strengths that make them ideal candidates for Simple language bindings.

**Key Findings:**
- Genesis: 100% Python, 10-80x faster than Isaac Gym, unified multi-physics solver architecture
- Isaac Lab: NVIDIA's successor to Isaac Gym, PhysX-based, direct GPU tensor API, photorealistic rendering
- Both support batched parallel simulation (1000s of environments on single GPU)
- Simple's unique features (GPU/SIMD, units, effect system, actor model) align perfectly with physics simulation needs
- FFI integration paths identified for both Python and native C/CUDA backends

---

## 1. Genesis Physics Engine

### 1.1 Overview

[Genesis](https://genesis-world.readthedocs.io/) is "a generative world for general-purpose robotics & embodied AI learning" that combines a universal physics engine, simulation platform, rendering system, and generative data engine. Released in December 2024, Genesis has quickly gained attention for its exceptional performance and Python-first design.

**Key Characteristics:**
- **100% Python Implementation:** Both front-end API and back-end physics engine written in pure Python
- **Cross-Platform:** Linux, macOS, Windows with CPU, NVIDIA, AMD, and Apple Metal backend support
- **Ultra-Fast:** 430,000x faster than real-time (43M FPS on single Franka arm scene with RTX 4090)
- **10-80x faster** than Isaac Gym/MuJoCo MJX according to [performance benchmarks](https://www.datacamp.com/blog/genesis-physics-engine)
- **Open Source:** [GitHub repository](https://github.com/Genesis-Embodied-AI/Genesis)

### 1.2 Architecture and Core Concepts

#### Physics Solver Architecture

Genesis implements a **unified multi-physics framework** that integrates diverse state-of-the-art physics solvers:

| Solver | Purpose | Status |
|--------|---------|--------|
| **Rigid Body** | Articulated systems, robots, rigid objects | ✅ Implemented |
| **MPM** (Material Point Method) | Granular materials, snow, sand | ✅ Differentiable |
| **SPH** (Smoothed Particle Hydrodynamics) | Fluids, liquids | ✅ Implemented |
| **FEM** (Finite Element Method) | Deformable objects, soft bodies | ✅ Implemented |
| **PBD** (Position Based Dynamics) | Cloth, ropes, soft constraints | ✅ Implemented |
| **Stable Fluid** | Gases, smoke, atmospheric effects | ✅ Implemented |
| **Tool Solver** | Differentiable tool interactions | ✅ Differentiable |

**Solver Coupling:** Genesis's key innovation is the ability to seamlessly couple different physics solvers within a unified framework. For example, simulating a robot (rigid body) manipulating liquid (SPH) in a deformable container (FEM) on granular terrain (MPM).

#### Compute Backend: Taichi

Genesis uses [Taichi](https://www.taichi-lang.org/) as its high-performance cross-platform compute backend:

- **Taichi Version:** Requires 1.7.x
- **GPU Kernels:** Prepares and optimizes GPU kernels for both rendering and physics calculations
- **JIT Compilation:** Taichi compiles Python code to optimized GPU kernels at runtime
- **Cross-Backend:** Single codebase runs on CUDA, Metal, Vulkan, CPU

**Performance Optimizations:**
- Optimized collision checking
- Auto-hibernation for inactive objects
- Contact island detection
- Parallel computation across all physics solvers

### 1.3 API Surface and Scene Creation

#### Python API Design

Genesis emphasizes simplicity and user-friendliness with an intuitive API:

```python
import genesis as gs

# Initialize with backend selection
gs.init(backend=gs.cuda)  # or gs.cpu, gs.metal, gs.vulkan

# Create scene
scene = gs.Scene()

# Add entities
plane = scene.add_entity(gs.morphs.Plane())
robot = scene.add_entity(
    gs.morphs.MJCF(file='franka_emika_panda/panda.xml')
)

# Add physics materials
liquid = scene.add_entity(
    gs.morphs.Box(size=[0.1, 0.1, 0.1]),
    material=gs.materials.SPH(density=1000.0, viscosity=0.01)
)

# Build and simulate
scene.build()

for i in range(1000):
    scene.step()
```

#### Material System

Genesis supports a wide range of material models with physics-specific parameters:

- **Rigid Materials:** Mass, inertia, friction, restitution
- **Fluid Materials (SPH):** Density, viscosity, surface tension
- **Deformable Materials (FEM):** Young's modulus, Poisson ratio
- **Granular Materials (MPM):** Particle properties, friction angle
- **Cloth Materials (PBD):** Stretch/bend stiffness, damping

#### Generative Capabilities

Genesis includes a **generative data engine** that can transform natural language descriptions into:
- Interactive scenes
- Task proposals and reward functions
- Robot behaviors and policies
- Character motions and trajectories
- Camera motion sequences

This is achieved through integration with large language models, though the full generative framework is marked as "forthcoming" in version 0.3.3.

### 1.4 GPU Acceleration Implementation

#### Performance Characteristics

According to [DataCamp's analysis](https://www.datacamp.com/tutorial/genesis-physics-engine-tutorial):

**Benchmark Results (RTX 4090):**
- Simple manipulation scene: 43M FPS (430,000x real-time)
- Complex multi-body systems: 10-80x faster than Isaac Gym
- Soft body simulation: Comparable or faster than specialized engines

**Scalability:**
- Thousands of parallel environments on single GPU
- Efficient batch processing across all solvers
- Automatic load balancing and hibernation

#### Memory Management

Genesis leverages Taichi's memory management:
- GPU memory pooling and reuse
- Automatic memory transfer between CPU/GPU
- Sparse data structures for collision detection
- Efficient particle-grid transfers for MPM/SPH

### 1.5 Simulation Types Supported

#### Rigid Body Dynamics

- **Articulated Systems:** Full support for URDF/MJCF robot descriptions
- **Joint Types:** Revolute, prismatic, spherical, fixed, free
- **Contact Handling:** Optimized collision detection with contact islands
- **Constraints:** Position/velocity constraints, motors, limits

#### Soft Body Simulation

- **FEM-Based:** Tetrahedral meshes with various constitutive models
- **Hybrid Robots:** Soft skins with rigid skeletons (bio-inspired designs)
- **Coupling:** Rigid-soft interaction through unified contact handling

#### Fluid Simulation

- **SPH Solver:** Particle-based fluids with surface tension
- **Stable Fluid:** Grid-based gas/smoke simulation
- **Free Surface:** Automatic air-fluid boundary detection
- **Rigid-Fluid Coupling:** Buoyancy, drag, fluid forces on rigid bodies

#### Granular Materials

- **MPM Solver:** Continuum approach to granular flow
- **Material Models:** Drucker-Prager, von Mises plasticity
- **Applications:** Sand, soil, snow simulation
- **Differentiable:** Full gradient support for optimization

### 1.6 Integration with Robotics Workflows

#### Robot Description Formats

- **MJCF:** MuJoCo XML format (primary)
- **URDF:** ROS Unified Robot Description Format
- **Custom Morphs:** Programmatic robot construction

#### Sensor Support

- **Proprioception:** Joint positions, velocities, forces
- **Cameras:** RGB, depth, segmentation (ray tracing or rasterization)
- **Contact Sensors:** Force/torque at contact points
- **Inertial:** Accelerometer, gyroscope data

#### Control Interfaces

- **Position Control:** Joint position targets with PD control
- **Velocity Control:** Joint velocity targets
- **Torque Control:** Direct torque application
- **Hybrid:** Mixed control modes per joint

#### RL Environment Integration

Genesis provides Gym-compatible interfaces:

```python
env = gs.envs.Franka(
    num_envs=4096,  # Parallel environments
    obs_mode='state',  # or 'rgb', 'depth'
    control_mode='joint_position'
)

obs = env.reset()
for _ in range(1000):
    action = policy(obs)
    obs, reward, done, info = env.step(action)
```

### 1.7 Performance Characteristics

#### Benchmarking Data

From [Genesis announcement](https://genesis-embodied-ai.github.io/) and [MarkTechPost coverage](https://www.marktechpost.com/2024/12/19/meet-genesis-an-open-source-physics-ai-engine-redefining-robotics-with-ultra-fast-simulations-and-generative-4d-worlds/):

**Single Scene Performance:**
- Franka arm + plane: 43M FPS (RTX 4090)
- 100 rigid bodies: 8M FPS
- 10K particles (SPH): 2M FPS
- 1K deformable bodies: 500K FPS

**Parallel Environments:**
- 4096 Franka envs: 1.2M total FPS (293 FPS per env)
- 16K simple envs: 4M total FPS (244 FPS per env)

**Comparison with Other Engines:**
- Isaac Gym: 10-80x slower on equivalent tasks
- MuJoCo MJX: 15-50x slower
- PyBullet: 100-1000x slower

---

## 2. Isaac Lab/Gym (NVIDIA)

### 2.1 Overview and Evolution

#### Isaac Gym (Deprecated)

[Isaac Gym](https://developer.nvidia.com/isaac-gym) was NVIDIA's prototype GPU-based physics simulation environment for reinforcement learning research. Key characteristics:

- **Standalone System:** Did not integrate with broader NVIDIA ecosystem
- **Python API:** Custom APIs for environment setup
- **PhysX Backend:** GPU-accelerated rigid body dynamics
- **Basic Rendering:** No ray tracing or advanced sensors
- **Status:** Preview Release 4.0 (deprecated as of 2024)

#### Isaac Sim

[Isaac Sim](https://developer.nvidia.com/isaac/sim) is NVIDIA's production robotics simulation platform:

- **Omniverse Foundation:** Built on NVIDIA Omniverse platform
- **USD-Based:** Uses Pixar's Universal Scene Description
- **PhysX + RTX:** High-fidelity physics and photorealistic rendering
- **Comprehensive Sensors:** Cameras, LiDAR, IMU with realistic physics
- **ROS Integration:** Direct ROS/ROS2 connectivity

**Latest Version (2025):** Isaac Sim 4.5/5.0 with improved URDF import, joint visualization, and NVIDIA Cosmos integration.

#### Isaac Lab

[Isaac Lab](https://developer.nvidia.com/isaac/lab) is "the natural successor to Isaac Gym" and "extends GPU-native robotics simulation into the era of large-scale multi-modal learning."

**Official Definition (from [NVIDIA Research](https://research.nvidia.com/publication/2025-09_isaac-lab-gpu-accelerated-simulation-framework-multi-modal-robot-learning)):**
> "Isaac Lab combines high-fidelity GPU parallel physics, photorealistic rendering, and a modular, composable architecture for designing environments and training robot policies."

**Key Features:**
- Built on Isaac Sim (PhysX + RTX)
- GPU-native end-to-end pipeline
- Multi-modal learning support (vision, touch, proprioception)
- Open source: [GitHub](https://github.com/isaac-sim/IsaacLab)
- Latest: Isaac Lab 2.2 (SIGGRAPH 2025)

### 2.2 Architecture

#### Layered Architecture

Isaac Lab implements a modular architecture with clear separation of concerns:

```
┌─────────────────────────────────────────────────┐
│           Learning Framework Layer              │
│     (RL/IL algorithms: stable-baselines3,       │
│      rsl_rl, skrl, etc.)                        │
└─────────────────────────────────────────────────┘
                      ↓
┌─────────────────────────────────────────────────┐
│         Isaac Lab Environment Layer             │
│   - ManagerBasedEnv / ManagerBasedRLEnv         │
│   - Observation/Action/Reward Managers          │
│   - Scene composition and asset management      │
└─────────────────────────────────────────────────┘
                      ↓
┌─────────────────────────────────────────────────┐
│          Isaac Sim Core Layer                   │
│   - PhysX (rigid/deformable physics)            │
│   - RTX (ray-traced rendering)                  │
│   - USD (scene description)                     │
│   - OmniPhysics Tensor API                      │
└─────────────────────────────────────────────────┘
```

#### Core Components

**Environment Abstractions:**
- `ManagerBasedEnv`: Basic environment for robot control (no RL-specific features)
- `ManagerBasedRLEnv`: Extends ManagerBasedEnv with rewards, terminations, curriculum
- `DirectRLEnv`: Lower-level API for maximum performance

**Manager System:**
- **Scene Manager:** Handles entity creation, cloning, reset
- **Observation Manager:** Computes and groups observations (policy/critic)
- **Action Manager:** Processes actions into low-level commands
- **Reward Manager:** Computes reward terms and aggregates
- **Termination Manager:** Checks termination conditions
- **Command Manager:** Generates task commands (goals, velocities)
- **Curriculum Manager:** Adapts difficulty over training

### 2.3 PhysX and GPU Acceleration

#### PhysX Engine Capabilities

According to [Isaac Lab documentation](https://isaac-sim.github.io/IsaacLab/main/source/setup/walkthrough/technical_env_design.html):

**Physics Features:**
- **Rigid Body Dynamics:** Articulated systems with reduced coordinates
- **Deformable Objects:** Cloth, soft bodies with coupled rigid-deformable solver
- **Contact Handling:** Filtered contact reporting, advanced friction models
- **Joint Types:** Revolute, prismatic, spherical, D6 (6-DOF)
- **Kinematic Chains:** Closed-loop chains, mimic joints
- **GPU Acceleration:** Entire physics pipeline runs on GPU

**Enhancements over Isaac Gym:**
- Filtered contact reporting (specific body pairs)
- Mimic joint systems (coupled joints)
- Closed-loop kinematic chains
- Deformable object support
- Improved stability and performance

#### Direct GPU API

From [PhysX documentation](https://nvidia-omniverse.github.io/PhysX/physx/5.4.0/docs/DirectGPUAPI.html) and [Isaac Lab paper](https://arxiv.org/html/2511.04831v1):

**OmniPhysics Tensor API:**
- **Direct Access:** Read/write simulation state in GPU memory without CPU transfer
- **Batched Views:** Organized access to arrays of objects (all robots, all links)
- **Type Safety:** Strongly-typed view classes (ArticulationView, RigidBodyView)
- **Zero-Copy:** CUDA tensors reference GPU memory directly

**Key Difference from Isaac Gym:**
- Isaac Gym: Raw buffer access with manual indexing
- Isaac Lab: Structured view APIs with automatic batching

**Example:**
```python
# Isaac Lab approach
robot = Articulation(...)  # High-level articulation object
robot_data = robot.data    # ArticulationData view

# Direct GPU tensor access (zero-copy)
joint_pos = robot_data.joint_positions  # [num_envs, num_joints] tensor on GPU
joint_vel = robot_data.joint_velocities

# Write back to simulation (stays on GPU)
robot_data.joint_position_targets = desired_positions
```

### 2.4 API Surface and Tensor Interface

#### Environment Creation

From [Isaac Lab tutorials](https://isaac-sim.github.io/IsaacLab/main/source/tutorials/03_envs/create_manager_base_env.html):

```python
import isaaclab.envs as envs
from isaaclab.envs import ManagerBasedRLEnv, ManagerBasedRLEnvCfg

# Define environment configuration
@dataclass
class MyEnvCfg(ManagerBasedRLEnvCfg):
    # Scene configuration
    scene: SceneCfg = SceneCfg(num_envs=4096, env_spacing=2.0)

    # Observation manager
    observations: ObservationsCfg = ObservationsCfg()

    # Action manager
    actions: ActionsCfg = ActionsCfg()

    # Reward manager
    rewards: RewardsCfg = RewardsCfg()

# Create environment
env = ManagerBasedRLEnv(cfg=MyEnvCfg())
```

#### Observation Spaces

From [Isaac Lab API docs](https://isaac-sim.github.io/IsaacLab/main/source/api/lab/isaaclab.envs.html):

**Observation Structure:**
- Returns dictionary with "policy" and "critic" keys (asymmetric actor-critic)
- Each group contains multiple observation terms
- Can use Gymnasium spaces or Python types for definition

**Example:**
```python
@dataclass
class ObservationsCfg:
    @dataclass
    class PolicyCfg(ObsGroup):
        # Joint positions (num_envs, num_joints)
        joint_pos = ObsTerm(func=get_joint_positions)

        # Joint velocities
        joint_vel = ObsTerm(func=get_joint_velocities)

        # End-effector pose
        ee_pose = ObsTerm(func=get_ee_pose)

        def __post_init__(self):
            self.concatenate_terms = True  # Flatten to single tensor

    policy: PolicyCfg = PolicyCfg()
```

**Tensor-Based Returns:**
- All observations are PyTorch tensors on GPU
- Shape: [num_envs, observation_dim]
- No CPU transfer required for policy inference

#### Action Spaces

From [Isaac Lab GitHub discussions](https://github.com/isaac-sim/IsaacLab/discussions/1264):

**Action Manager Hierarchy:**
- **Raw Actions:** What the learning algorithm outputs
- **Action Terms:** Individual action components (joints, grippers)
- **Processed Actions:** Converted to simulation commands

**Control Modes:**
- **Joint Position:** PD controller with position targets
- **Joint Velocity:** PD controller with velocity targets
- **Joint Effort:** Direct torque control
- **Task Space:** IK-based end-effector control

**Example:**
```python
@dataclass
class ActionsCfg:
    # Joint position control
    joint_actions = ActionTerm(
        asset_name="robot",
        joint_names=["joint_.*"],  # Regex pattern
        control_mode="position",
        scale=0.5  # Action scaling
    )
```

#### Tensor Interface Details

From [Isaac Gym Tensor API docs](https://docs.robotsfan.com/isaacgym/programming/tensors.html):

**Key Principles:**
- All data is batched across environments (first dimension = num_envs)
- Tensors remain on GPU throughout training loop
- Views provide structured access to simulation state
- Direct modification of tensors updates simulation

**ArticulationData Fields:**
```python
joint_positions        # [num_envs, num_joints]
joint_velocities       # [num_envs, num_joints]
joint_accelerations    # [num_envs, num_joints]
root_pos_w            # [num_envs, 3]
root_quat_w           # [num_envs, 4]
body_pos_w            # [num_envs, num_bodies, 3]
body_quat_w           # [num_envs, num_bodies, 4]
```

### 2.5 Parallel Simulation and Batching

#### Massive Parallelism

From [Isaac Lab research paper](https://d1qx31qr3h6wln.cloudfront.net/publications/Isaac%20Lab,%20A%20GPU-Accelerated%20Simulation%20Framework%20for%20Multi-Modal%20Robot%20Learning.pdf):

**Performance Metrics:**
- **Environment Throughput:** Up to 1.6M frames per second
- **Typical Scales:** 2K-16K parallel environments on single A100/H100 GPU
- **Memory Efficiency:** ~100-500 MB per environment (depends on complexity)

**Batching Strategy:**
- Physics simulation batched at PhysX level (single kernel launch)
- Rendering batched using tiled pipeline (thousands of cameras)
- Observation computation vectorized across all environments
- Reward computation fully parallel (element-wise operations)

#### Tiled Rendering

For camera-rich environments (e.g., multi-view manipulation):

- **Traditional:** N cameras = N render passes
- **Tiled:** N cameras arranged as tiles in single framebuffer
- **Result:** ~10x speedup for 100+ cameras

**Example Use Case:**
- 4096 environments, 4 cameras each = 16,384 cameras
- Tiled rendering: ~30 FPS
- Traditional rendering: ~3 FPS

#### Multi-GPU and Multi-Node

From [Isaac Lab multi-GPU docs](https://isaac-sim.github.io/IsaacLab/main/source/features/multi_gpu.html):

**Distributed Training:**
- Each process instantiates independent simulation environment
- Standard distributed RL frameworks (Ray, torch.distributed)
- Linear scaling up to 8 GPUs (communication bottleneck beyond)

**Configuration:**
```python
# Launch with torchrun
# torchrun --nproc_per_node=4 train.py

env = ManagerBasedRLEnv(cfg=MyEnvCfg())
# Automatically detects distributed setting
```

### 2.6 USD and PhysX Integration

#### Universal Scene Description (USD)

USD provides the foundation for Isaac Sim's scene representation:

- **Hierarchical:** Scene graph with prims (primitives)
- **Layered:** Non-destructive overrides and variants
- **Extensible:** Custom schemas and properties
- **Interoperable:** Exchange with DCC tools (Blender, Maya, Houdini)

**For High-Performance RL:**
- USD read/write bypassed during simulation
- Initial scene setup only
- Direct tensor API for runtime access

#### PhysX Schema

Isaac Sim extends USD with PhysX-specific schemas:

- **PhysicsScene:** Global physics settings (gravity, timestep)
- **PhysicsRigidBody:** Rigid body properties (mass, inertia)
- **PhysicsCollision:** Collision geometry and materials
- **PhysicsJoint:** Joint definitions and limits
- **PhysicsArticulation:** Articulated system settings

### 2.7 Performance Characteristics

#### Benchmarking (2025)

From [Isaac Lab announcement](https://developer.nvidia.com/blog/isaac-sim-and-isaac-lab-are-now-available-for-early-developer-preview/):

**Training Performance (on A100):**
- Humanoid locomotion: 120M samples/hour (4096 envs)
- Shadow hand manipulation: 80M samples/hour (8192 envs)
- Quadruped terrain: 150M samples/hour (4096 envs)

**Comparison:**
- Isaac Gym Preview 4: Baseline
- Isaac Lab: 1.2-1.5x faster (improved PhysX, tensor API)
- CPU-based (MuJoCo): 100-500x slower

**Rendering Performance:**
- RGB cameras: 30 FPS (4096 envs, 1 camera each, 256x256)
- Depth cameras: 60 FPS (same setup)
- Tiled rendering: Up to 100 FPS with many small views

---

## 3. Common Interface Design

### 3.1 Unified Abstractions

Both Genesis and Isaac Lab share core concepts despite different implementations. A Simple language binding can provide a unified interface that abstracts over both engines.

#### Scene/World Representation

**Concept:** Container for all simulation entities, physics settings, and rendering configuration.

**Common API:**
```simple
# Simple language concept
struct PhysicsScene:
    # Configuration
    timestep: #Duration
    gravity: Vec3<#Acceleration>
    num_envs: i32

    # Builder pattern
    fn builder() -> SceneBuilder:
        SceneBuilder::new()

    fn add_entity(entity: Entity) -> EntityHandle:
        # Add to scene graph

    fn step():
        # Advance simulation by one timestep

    fn reset(env_ids: Option<Array<i32>>):
        # Reset specific or all environments

# Backend-agnostic usage
let scene = PhysicsScene::builder()
    .timestep(#Duration::from_millis(10))
    .gravity(Vec3::new(0.0, 0.0, #Acceleration::from_m_s2(-9.81)))
    .num_envs(4096)
    .backend(Backend::Genesis)  # or Backend::IsaacLab
    .build()
```

**Mapping:**
- Genesis: `gs.Scene()`
- Isaac Lab: `ManagerBasedEnv` with `SceneCfg`

#### Rigid Body Dynamics

**Concept:** Rigid objects with mass, inertia, and collision geometry.

**Common Properties:**
- **Transform:** Position, orientation (quaternion or rotation matrix)
- **Dynamics:** Linear/angular velocity, acceleration
- **Inertial:** Mass, center of mass, inertia tensor
- **Material:** Friction coefficients, restitution, contact properties

**Simple API:**
```simple
struct RigidBody:
    # Physical properties
    mass: #Mass
    inertia: Mat3<#MomentOfInertia>
    friction: f32  # Dimensionless
    restitution: f32  # Dimensionless

    # State (batched across environments)
    position: Tensor<Vec3<#Length>, [NumEnvs]>
    orientation: Tensor<Quat, [NumEnvs]>
    linear_velocity: Tensor<Vec3<#Velocity>, [NumEnvs]>
    angular_velocity: Tensor<Vec3<#AngularVelocity>, [NumEnvs]>

    # Forces
    fn apply_force(force: Vec3<#Force>, at_point: Vec3<#Length>):
        # Apply force at specific point

    fn apply_torque(torque: Vec3<#Torque>):
        # Apply torque around center of mass
```

**Type Safety:** Note the use of Simple's unit types (#Mass, #Force, #Torque) for physical quantities, preventing common errors like applying force where torque is expected.

#### Articulated Systems (Robots)

**Concept:** Multi-body systems connected by joints with kinematic trees.

**Common Structure:**
- **Links:** Individual rigid bodies in the chain
- **Joints:** Connections between links (revolute, prismatic, etc.)
- **Actuators:** Motors that drive joint motion
- **Sensors:** Encoders, force/torque sensors

**Simple API:**
```simple
struct Articulation:
    # Description
    links: Array<Link>
    joints: Array<Joint>
    root_link: LinkHandle

    # State (batched)
    joint_positions: Tensor<#Angle, [NumEnvs, NumJoints]>
    joint_velocities: Tensor<#AngularVelocity, [NumEnvs, NumJoints]>
    joint_forces: Tensor<#Torque, [NumEnvs, NumJoints]>

    # Commands
    fn set_joint_position_targets(targets: Tensor<#Angle, [NumEnvs, NumJoints]>):
        # PD control to target positions

    fn set_joint_torques(torques: Tensor<#Torque, [NumEnvs, NumJoints]>):
        # Direct torque control

    # Kinematics
    fn forward_kinematics(link: LinkHandle) -> Tensor<Mat4, [NumEnvs]>:
        # Get link transform in world frame

    fn jacobian(link: LinkHandle) -> Tensor<Mat6xN, [NumEnvs]>:
        # Compute geometric Jacobian

enum JointType:
    Revolute(axis: Vec3)
    Prismatic(axis: Vec3)
    Spherical
    Fixed
    Free
```

**Mapping:**
- Genesis: `gs.morphs.MJCF(...)` or `gs.morphs.URDF(...)`
- Isaac Lab: `Articulation` class with `ArticulationData`

### 3.2 Collision Detection

**Concept:** Detecting and resolving interpenetration between objects.

**Common Elements:**
- **Collision Shapes:** Primitives (box, sphere, capsule) and meshes
- **Collision Layers:** Filtering what can collide with what
- **Contact Points:** Position, normal, depth, impulse
- **Contact Events:** Callbacks for begin/end contact

**Simple API:**
```simple
enum CollisionShape:
    Box(half_extents: Vec3<#Length>)
    Sphere(radius: #Length)
    Capsule(radius: #Length, height: #Length)
    Mesh(vertices: Array<Vec3<#Length>>, indices: Array<u32>)
    Heightfield(heights: Array2D<#Length>)

struct Collider:
    shape: CollisionShape
    offset: Transform  # Relative to parent body
    material: ContactMaterial

struct ContactMaterial:
    friction_static: f32
    friction_dynamic: f32
    restitution: f32

struct ContactPoint:
    position: Vec3<#Length>
    normal: Vec3  # Normalized direction
    depth: #Length
    impulse: Vec3<#Impulse>
    body_a: BodyHandle
    body_b: BodyHandle
```

**Backend Mapping:**
- Genesis: Collision shapes defined per solver (rigid body uses standard primitives)
- Isaac Lab: PhysX collision schemas with USD geometry

### 3.3 Constraints and Joints

**Concept:** Restricting relative motion between bodies.

**Joint Constraints:**
```simple
struct RevoluteJoint:
    axis: Vec3  # Rotation axis
    limits: (Option<#Angle>, Option<#Angle>)  # Min/max
    damping: #AngularDamping
    stiffness: #AngularStiffness
    max_torque: #Torque

struct PrismaticJoint:
    axis: Vec3  # Translation axis
    limits: (Option<#Length>, Option<#Length>)
    damping: #Damping
    stiffness: #Stiffness
    max_force: #Force

struct D6Joint:  # 6-DOF constraint
    locked_axes: Set<DOF>  # Which DOFs are locked
    limits: Map<DOF, (f32, f32)>
    drives: Map<DOF, Drive>
```

**Motors/Drives:**
```simple
struct Drive:
    target: f32  # Position or velocity
    stiffness: f32
    damping: f32
    max_force: f32  # Force or torque depending on joint type
```

### 3.4 Sensors and Observations

**Concept:** Extracting information from the simulation for perception and control.

#### Proprioceptive Sensors

**Joint Sensors:**
```simple
# Batched across all environments
struct JointSensor:
    fn measure_positions() -> Tensor<#Angle, [NumEnvs, NumJoints]>
    fn measure_velocities() -> Tensor<#AngularVelocity, [NumEnvs, NumJoints]>
    fn measure_efforts() -> Tensor<#Torque, [NumEnvs, NumJoints]>
```

**IMU (Inertial Measurement Unit):**
```simple
struct IMUSensor:
    fn measure_acceleration() -> Tensor<Vec3<#Acceleration>, [NumEnvs]>
    fn measure_angular_velocity() -> Tensor<Vec3<#AngularVelocity>, [NumEnvs]>
    fn measure_orientation() -> Tensor<Quat, [NumEnvs]>
```

**Force/Torque Sensors:**
```simple
struct FTSensor:
    fn measure_force() -> Tensor<Vec3<#Force>, [NumEnvs]>
    fn measure_torque() -> Tensor<Vec3<#Torque>, [NumEnvs]>
```

#### Exteroceptive Sensors

**Camera:**
```simple
enum CameraMode:
    RGB
    Depth
    Segmentation
    OpticalFlow

struct Camera:
    resolution: (u32, u32)
    fov: #Angle
    near: #Length
    far: #Length

    fn capture(mode: CameraMode) -> Tensor<f32, [NumEnvs, H, W, C]>
```

**LiDAR:**
```simple
struct LiDAR:
    range: #Length
    fov_horizontal: #Angle
    fov_vertical: #Angle
    num_rays: (u32, u32)  # Horizontal, vertical

    fn scan() -> Tensor<#Length, [NumEnvs, NumRays]>
```

#### Observation Manager

Unified interface for collecting and organizing observations:

```simple
struct ObservationManager:
    fn add_term(name: String, func: Fn() -> Tensor):
        # Add observation term

    fn compute() -> Map<String, Tensor>:
        # Compute all observations

    fn get_observation_space() -> Space:
        # Get Gym-style space definition
```

### 3.5 Action Spaces

**Concept:** Commands sent from policy to simulation.

#### Action Types

```simple
enum ActionType:
    # Joint-level
    JointPosition(targets: Tensor<#Angle, [NumEnvs, NumJoints]>)
    JointVelocity(targets: Tensor<#AngularVelocity, [NumEnvs, NumJoints]>)
    JointEffort(torques: Tensor<#Torque, [NumEnvs, NumJoints]>)

    # Task-space
    EndEffectorPose(poses: Tensor<Mat4, [NumEnvs]>)
    EndEffectorVelocity(velocities: Tensor<Vec6, [NumEnvs]>)

    # Hybrid
    Differential(base_vel: Tensor<Vec3<#Velocity>, [NumEnvs]>,
                 arm_joints: Tensor<#Angle, [NumEnvs, NumArmJoints]>)
```

#### Action Processing

```simple
struct ActionManager:
    fn process_raw_action(action: Tensor) -> ActionType:
        # Convert network output to simulation command

    fn apply(action_type: ActionType):
        # Apply to simulation entities
```

**Example Processing:**
1. **Normalize:** Network outputs [-1, 1]
2. **Scale:** Map to actual joint ranges
3. **Clip:** Enforce safety limits
4. **Filter:** Optional low-pass filter for smoothness
5. **Apply:** Set targets or torques

### 3.6 Parallel Simulation (Batched Environments)

**Concept:** Running thousands of independent simulation environments in parallel on GPU.

#### Batching Strategy

**Key Principle:** First dimension of all tensors is `num_envs`.

```simple
# All state is batched
struct BatchedSimulation:
    num_envs: i32

    # State for all environments
    robot_joint_pos: Tensor<#Angle, [NumEnvs, NumJoints]>
    robot_joint_vel: Tensor<#AngularVelocity, [NumEnvs, NumJoints]>
    object_pos: Tensor<Vec3<#Length>, [NumEnvs, NumObjects]>

    fn step(actions: Tensor<f32, [NumEnvs, ActionDim]>):
        # Single GPU kernel processes all envs in parallel

    fn reset(env_ids: Tensor<i32, [NumReset]>):
        # Reset subset of environments
```

#### Environment Cloning

**Setup:**
1. Create single reference environment (template)
2. Clone to GPU with spatial offsets
3. All clones share same entity definitions
4. Independent state per clone

**Simple API:**
```simple
let template = create_template_scene()

let batched = BatchedSimulation::from_template(
    template,
    num_envs=4096,
    spacing=#Length::from_meters(2.0)  # Spatial separation
)
```

**Spatial Layout:**
- Genesis: Automatic grid layout with configurable spacing
- Isaac Lab: Configurable patterns (grid, random, custom)

#### Selective Reset

**Concept:** Reset only terminated environments, keeping others running.

```simple
fn selective_reset(
    sim: mut BatchedSimulation,
    dones: Tensor<bool, [NumEnvs]>
):
    let reset_ids = dones.nonzero()  # [NumReset]
    sim.reset(reset_ids)
```

**Efficiency:**
- Only reset what's needed
- Maintains training throughput
- Avoids synchronization overhead

### 3.7 Reward Computation

**Concept:** Computing scalar rewards for RL from simulation state.

```simple
struct RewardManager:
    terms: Map<String, RewardTerm>

    fn compute_rewards(state: SimState) -> Tensor<f32, [NumEnvs]>:
        let total = Tensor::zeros([num_envs])
        for term in terms.values():
            total += term.weight * term.compute(state)
        return total

struct RewardTerm:
    weight: f32
    compute: Fn(SimState) -> Tensor<f32, [NumEnvs]>

# Example terms
fn distance_to_goal(state: SimState) -> Tensor<f32, [NumEnvs]>:
    let dist = (state.ee_pos - state.goal_pos).norm()
    return -dist  # Negative distance as reward

fn velocity_penalty(state: SimState) -> Tensor<f32, [NumEnvs]>:
    return -state.joint_vel.abs().sum(dim=1)  # Penalize high velocities
```

**Vectorization:** All reward computation fully vectorized across environments.

### 3.8 Termination Conditions

**Concept:** Detecting when an episode should end.

```simple
struct TerminationManager:
    fn check_terminations(state: SimState) -> Tensor<bool, [NumEnvs]>:
        let dones = Tensor::zeros_bool([num_envs])

        # Time limit
        dones |= state.step_count >= max_steps

        # Task success
        dones |= (state.ee_pos - state.goal_pos).norm() < threshold

        # Failure conditions
        dones |= state.robot_pos.z < min_height  # Fallen over
        dones |= state.joint_pos.abs() > joint_limits  # Joint limit violation

        return dones
```

---

## 4. Simple Language Unique Features

Simple's design philosophy and features make it exceptionally well-suited for physics simulation integration.

### 4.1 GPU/SIMD for Physics Computation

#### Native GPU Support

Simple's Vulkan backend and GPU kernel capabilities align perfectly with both Genesis and Isaac Lab's GPU-first architectures.

**Advantages:**
1. **Direct Kernel Authoring:** Write custom physics kernels in Simple
2. **Memory Control:** Explicit GPU memory management via effect system
3. **Cross-Platform:** Vulkan works on NVIDIA, AMD, Intel, Apple
4. **Type Safety:** Compile-time checks for GPU-safe code

**Example Custom Kernel:**
```simple
# GPU kernel for custom reward computation
@gpu_kernel
fn compute_distance_rewards(
    ee_positions: Tensor<Vec3<#Length>, [NumEnvs]>,
    goal_positions: Tensor<Vec3<#Length>, [NumEnvs]>,
    rewards: mut Tensor<f32, [NumEnvs]>
):
    let idx = gpu.thread_idx_x()
    let dist = (ee_positions[idx] - goal_positions[idx]).norm()
    rewards[idx] = -dist.as_meters()  # Convert #Length to f32
```

#### SIMD Vectorization

For CPU-side processing (preprocessing, postprocessing):

```simple
# SIMD-optimized observation preprocessing
@simd
fn normalize_observations(
    raw_obs: Tensor<f32, [NumEnvs, ObsDim]>,
    mean: Array<f32>,
    std: Array<f32>
) -> Tensor<f32, [NumEnvs, ObsDim]>:
    return (raw_obs - mean) / std  # Auto-vectorized
```

### 4.2 Unit Types for Physical Quantities

Simple's semantic unit types (#Force, #Torque, #Velocity, etc.) provide compile-time safety for physics simulation.

#### Type Safety Benefits

**Prevents Common Errors:**
```simple
# Compile error: can't assign force to torque
let torque: #Torque = #Force::from_newtons(10.0)  # ERROR

# Compile error: can't add force and mass
let result = force + mass  # ERROR

# Correct: units compose properly
let acceleration: #Acceleration = force / mass  # OK
let energy: #Energy = force * distance  # OK
```

#### Automatic Unit Conversion

```simple
# Different unit systems compose seamlessly
let force_si = #Force::from_newtons(100.0)
let force_imperial = #Force::from_pounds_force(22.48)
let total = force_si + force_imperial  # Automatic conversion

# Check equality with tolerance
assert(total.as_newtons() ≈ 200.0, tolerance=0.1)
```

#### Integration with Physics Engines

**Genesis/Isaac Lab Integration:**
```simple
# Simple wrapper around backend
struct SimpleRigidBody:
    backend: RigidBodyBackend  # Genesis or Isaac Lab

    fn apply_force(force: Vec3<#Force>, point: Vec3<#Length>):
        # Convert to backend's expected units (usually SI)
        let force_si = force.as_newtons()
        let point_si = point.as_meters()
        backend.apply_force_raw(force_si, point_si)

    fn get_velocity() -> Vec3<#Velocity>:
        let vel_si = backend.get_velocity_raw()  # Returns m/s
        return Vec3::new(
            #Velocity::from_m_s(vel_si.x),
            #Velocity::from_m_s(vel_si.y),
            #Velocity::from_m_s(vel_si.z)
        )
```

**Benefits:**
- Type-checked physics equations
- Explicit unit conversions at API boundaries
- No runtime overhead (units erased at compile time)
- Self-documenting code

#### Common Physics Units

From Simple's units specification:

| Quantity | Type | Base Units | Examples |
|----------|------|------------|----------|
| Length | #Length | meters | from_meters, from_mm, as_meters |
| Mass | #Mass | kilograms | from_kg, from_g, as_kg |
| Time | #Duration | seconds | from_secs, from_millis, as_secs |
| Force | #Force | newtons | from_newtons, from_lbf, as_newtons |
| Torque | #Torque | newton-meters | from_nm, as_nm |
| Velocity | #Velocity | m/s | from_m_s, from_km_h, as_m_s |
| Angular Velocity | #AngularVelocity | rad/s | from_rad_s, from_rpm, as_rad_s |
| Acceleration | #Acceleration | m/s² | from_m_s2, as_m_s2 |
| Angle | #Angle | radians | from_radians, from_degrees, as_radians |
| Energy | #Energy | joules | from_joules, from_kwh, as_joules |
| Power | #Power | watts | from_watts, from_hp, as_watts |

### 4.3 Effect System for Safe Concurrent Simulation

Simple's effect system (`async`, `nogc`, etc.) provides guarantees crucial for physics simulation.

#### Effect Annotations

**Key Effects:**
- `async`: Allows asynchronous operations (GPU kernel launch, I/O)
- `nogc`: No garbage collection (deterministic memory, real-time safe)
- `mut`: Allows mutation (vs. immutable pure functions)

**Physics Simulation Context:**
```simple
# High-performance simulation loop
@async @nogc
fn simulation_loop(
    scene: mut BatchedSimulation,
    policy: NeuralNetwork
):
    loop:
        # Async GPU kernel for sensor observation
        let obs = scene.compute_observations().await  # async

        # Neural network inference on GPU
        let actions = policy.forward(obs).await  # async

        # Step simulation (stays on GPU)
        scene.step(actions).await  # async

        # All memory pre-allocated, no GC
        # nogc effect ensures deterministic performance
```

#### Concurrency Safety

**Actor Model for Distributed Simulation:**
```simple
# Actor for managing a shard of environments
actor SimulationShard:
    shard_id: i32
    scene: BatchedSimulation
    policy: mut NeuralNetwork

    @async @nogc
    fn run_episodes(num_episodes: i32):
        for _ in 0..num_episodes:
            let obs = scene.reset()
            loop:
                let actions = policy.forward(obs).await
                obs, rewards, dones = scene.step(actions).await

                if dones.all():
                    break

# Spawn multiple shards on different GPUs
let shards = Array::new()
for gpu_id in 0..num_gpus:
    let shard = SimulationShard::spawn(
        shard_id=gpu_id,
        scene=create_scene(gpu_id),
        policy=load_policy()
    )
    shards.push(shard)
```

**Benefits:**
- **Isolation:** Each actor owns its simulation shard
- **No Data Races:** Actor model prevents shared mutable state
- **Async Coordination:** Actors communicate via messages
- **Multi-GPU:** Natural fit for multi-GPU scaling

### 4.4 Memory Safety Without GC Overhead

#### Deterministic Performance

**Problem with GC in Real-Time Simulation:**
- Unpredictable pause times
- Memory fragmentation
- Throughput variance

**Simple's Solution:**
```simple
@nogc  # Opt out of garbage collection
fn physics_step(state: mut SimState):
    # All allocations from arena/pool
    # No GC pauses
    # Deterministic timing
```

#### Arena Allocation

**Pre-allocated Memory Pools:**
```simple
# Setup phase (with GC allowed)
fn create_simulation() -> BatchedSimulation:
    let arena = Arena::new(capacity=#ByteCount::from_gb(4))

    # All simulation data allocated from arena
    let scene = BatchedSimulation::new_in(arena, num_envs=4096)

    return scene

# Runtime (nogc)
@nogc
fn run(scene: mut BatchedSimulation):
    # Uses pre-allocated memory only
    # No dynamic allocation
    # No GC
```

#### Ownership and Borrowing

**Compile-Time Memory Safety:**
```simple
fn safe_physics_update(body: mut RigidBody):
    # Exclusive mutable borrow
    body.apply_force(force, point)

# Compile error: can't borrow body mutably twice
fn invalid(body: mut RigidBody):
    let ref1 = &mut body  # First mutable borrow
    let ref2 = &mut body  # ERROR: already borrowed
```

**Benefits:**
- No runtime overhead
- No null pointer dereferences
- No use-after-free
- No data races

---

## 5. Implementation Strategy

### 5.1 FFI to C/C++/CUDA Libraries

#### Architecture Layers

```
┌─────────────────────────────────────────┐
│     Simple Application Code             │
│  (Type-safe, high-level API)            │
└─────────────────────────────────────────┘
                  ↓
┌─────────────────────────────────────────┐
│    Simple Physics Library (lib/std)     │
│  - Unified abstractions                 │
│  - Backend-agnostic API                 │
│  - Unit types for safety                │
└─────────────────────────────────────────┘
                  ↓
        ┌─────────┴──────────┐
        ↓                    ↓
┌──────────────┐    ┌──────────────────┐
│Genesis FFI   │    │Isaac Lab FFI     │
│Bindings      │    │Bindings          │
└──────────────┘    └──────────────────┘
        ↓                    ↓
┌──────────────┐    ┌──────────────────┐
│Genesis       │    │Isaac Sim/PhysX   │
│(Taichi/PyO3) │    │(USD/PhysX/RTX)   │
└──────────────┘    └──────────────────┘
```

#### Genesis FFI Strategy

**Challenge:** Genesis is pure Python (not C/C++ library)

**Options:**

**Option 1: Python Interop via PyO3-style Binding**
```rust
// In Rust (Simple's compiler backend)
use pyo3::prelude::*;

#[pyclass]
struct GenesisScene {
    py_scene: PyObject,
}

#[pymethods]
impl GenesisScene {
    #[new]
    fn new(num_envs: i32) -> PyResult<Self> {
        Python::with_gil(|py| {
            let gs = py.import("genesis")?;
            gs.call_method0("init")?;

            let scene_class = gs.getattr("Scene")?;
            let scene = scene_class.call0()?;

            Ok(GenesisScene {
                py_scene: scene.into(),
            })
        })
    }

    fn step(&self) -> PyResult<()> {
        Python::with_gil(|py| {
            self.py_scene.call_method0(py, "step")?;
            Ok(())
        })
    }
}
```

**Simple Language FFI:**
```simple
# Declare external (FFI) functions
extern fn genesis_create_scene(num_envs: i32) -> GenesisSceneHandle
extern fn genesis_step(scene: GenesisSceneHandle)
extern fn genesis_get_state(scene: GenesisSceneHandle, out: mut Tensor<f32>)

# High-level wrapper
struct GenesisBackend:
    handle: GenesisSceneHandle

    fn step():
        genesis_step(handle)
```

**Option 2: Direct Taichi Kernel Interop**

Since Genesis uses Taichi, we could potentially:
1. Extract Taichi kernels from Genesis
2. Call Taichi C API directly from Simple
3. Bypass Python overhead for performance-critical paths

**Benefits:**
- Lower overhead than Python interop
- Direct GPU memory access

**Challenges:**
- Requires understanding Genesis internals
- May break with Genesis updates
- More complex to maintain

#### Isaac Lab FFI Strategy

**Easier:** Isaac Sim/PhysX have C++ APIs

**Option 1: USD + PhysX C++ SDK**
```cpp
// C++ side (Isaac Sim SDK)
extern "C" {
    struct IsaacSceneHandle;

    IsaacSceneHandle* isaac_create_scene(int num_envs, const char* usd_path);
    void isaac_step(IsaacSceneHandle* scene);
    void isaac_get_joint_positions(IsaacSceneHandle* scene, float* out, int size);
    void isaac_set_joint_targets(IsaacSceneHandle* scene, const float* targets, int size);
    void isaac_destroy_scene(IsaacSceneHandle* scene);
}
```

**Simple FFI:**
```simple
# Opaque handle to C++ object
type IsaacSceneHandle = extern_type

extern fn isaac_create_scene(num_envs: i32, usd_path: CString) -> IsaacSceneHandle
extern fn isaac_step(scene: IsaacSceneHandle)
extern fn isaac_get_joint_positions(
    scene: IsaacSceneHandle,
    out: mut Array<f32>,
    size: i32
)

# Safe wrapper
struct IsaacLabBackend:
    handle: IsaacSceneHandle
    num_envs: i32
    num_joints: i32

    fn get_joint_positions() -> Tensor<#Angle, [NumEnvs, NumJoints]>:
        let raw = Array::new_zeroed(num_envs * num_joints)
        isaac_get_joint_positions(handle, mut raw, raw.len())

        # Convert to typed tensor
        return Tensor::from_raw(raw)
            .reshape([num_envs, num_joints])
            .map(|x| #Angle::from_radians(x))
```

**Option 2: PhysX Tensor API Direct Access**

For maximum performance, access PhysX GPU tensors directly:

```cpp
// C++ side
extern "C" {
    // Return CUDA device pointer
    void isaac_get_joint_positions_gpu(
        IsaacSceneHandle* scene,
        void** device_ptr,
        int* pitch,
        int* num_envs,
        int* num_joints
    );
}
```

```simple
# Simple side - zero-copy GPU access
fn get_joint_positions_gpu() -> GpuTensor<f32, [NumEnvs, NumJoints]>:
    let device_ptr: mut DevicePtr
    let pitch: i32
    let envs: i32
    let joints: i32

    isaac_get_joint_positions_gpu(
        handle,
        mut &device_ptr,
        mut &pitch,
        mut &envs,
        mut &joints
    )

    # Wrap as Simple GPU tensor (zero-copy)
    return GpuTensor::from_device_ptr(
        device_ptr,
        shape=[envs, joints],
        pitch=pitch
    )
```

**Benefits:**
- Zero-copy access to simulation data
- No CPU-GPU transfers
- Same memory layout as PhysX

### 5.2 Python Interop Layer

For Genesis (and potentially Isaac Lab Python API), we need robust Python interop.

#### PyO3-Inspired FFI

**Rust Side (in Simple's compiler):**
```rust
// src/runtime/src/python_ffi.rs
use pyo3::prelude::*;

pub struct PythonRuntime {
    gil: GILPool,
}

impl PythonRuntime {
    pub fn new() -> PyResult<Self> {
        pyo3::prepare_freethreaded_python();
        Ok(PythonRuntime {
            gil: Python::acquire_gil(),
        })
    }

    pub fn call_method(
        &self,
        obj: &PyObject,
        name: &str,
        args: &[PyObject]
    ) -> PyResult<PyObject> {
        let py = self.gil.python();
        obj.call_method(py, name, args, None)
    }
}

// Expose to Simple via FFI
#[no_mangle]
pub extern "C" fn simple_python_init() -> *mut PythonRuntime {
    Box::into_raw(Box::new(PythonRuntime::new().unwrap()))
}

#[no_mangle]
pub extern "C" fn simple_python_call_method(
    runtime: *mut PythonRuntime,
    obj: *mut PyObject,
    name: *const c_char,
    args: *const *mut PyObject,
    num_args: usize,
    out: *mut *mut PyObject
) -> i32 {
    // Safe wrapper around PyO3 calls
    // Returns error code
}
```

**Simple Side:**
```simple
# Python object wrapper
struct PyObject:
    handle: PyObjectHandle  # Opaque pointer to PyObject*

    fn call_method(name: String, args: Array<PyObject>) -> PyObject:
        let out: PyObjectHandle
        let err = simple_python_call_method(
            python_runtime,
            handle,
            name.as_cstr(),
            args.as_ptr(),
            args.len(),
            mut &out
        )

        if err != 0:
            panic("Python error: {}", get_python_exception())

        return PyObject(handle=out)

    fn to_tensor() -> Tensor<f32>:
        # Convert numpy array to Simple tensor
        let shape = get_array_shape()
        let data = get_array_data()
        return Tensor::from_raw(data, shape)
```

#### Genesis-Specific Bindings

```simple
# High-level Genesis API
struct Genesis:
    @static
    fn init(backend: BackendType):
        let gs = import_python_module("genesis")
        match backend:
            BackendType::CUDA => gs.call_method("init", [gs.cuda])
            BackendType::CPU => gs.call_method("init", [gs.cpu])

    @static
    fn create_scene(num_envs: i32) -> GenesisScene:
        let gs = import_python_module("genesis")
        let scene_class = gs.get_attr("Scene")
        let scene = scene_class.call()
        return GenesisScene(py_scene=scene)

struct GenesisScene:
    py_scene: PyObject

    fn add_entity(morph: Morph) -> EntityHandle:
        let entity = py_scene.call_method("add_entity", [morph.to_py()])
        return EntityHandle(py_obj=entity)

    fn step():
        py_scene.call_method("step", [])

    fn get_state() -> SimState:
        # Extract state from Python objects
        let state_dict = py_scene.get_attr("state").to_dict()

        # Convert to Simple tensors
        return SimState(
            joint_pos=state_dict.get("joint_pos").to_tensor(),
            joint_vel=state_dict.get("joint_vel").to_tensor(),
            # ...
        )
```

### 5.3 Build System Integration

#### Cargo Integration

**Cargo.toml additions:**
```toml
[dependencies]
pyo3 = { version = "0.20", features = ["auto-initialize"] }
numpy = "0.20"  # For numpy array conversion

# Isaac Sim SDK (C++)
physx-sys = { path = "crates/physx-sys" }  # Custom bindgen crate
usd-sys = { path = "crates/usd-sys" }

# Vulkan for Simple GPU backend
vulkan-rs = "0.37"
```

#### Custom Build Scripts

**For Isaac Lab bindings:**
```rust
// crates/physx-sys/build.rs
use std::env;
use std::path::PathBuf;

fn main() {
    let isaac_sdk_path = env::var("ISAAC_SDK_PATH")
        .expect("ISAAC_SDK_PATH must be set");

    println!("cargo:rustc-link-search={}/lib", isaac_sdk_path);
    println!("cargo:rustc-link-lib=PhysX");
    println!("cargo:rustc-link-lib=PhysXCommon");
    println!("cargo:rustc-link-lib=PhysXFoundation");

    // Generate bindings
    let bindings = bindgen::Builder::default()
        .header(format!("{}/include/physx/PxPhysicsAPI.h", isaac_sdk_path))
        .parse_callbacks(Box::new(bindgen::CargoCallbacks))
        .generate()
        .expect("Unable to generate bindings");

    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("physx_bindings.rs"))
        .expect("Couldn't write bindings!");
}
```

#### Simple Package Configuration

**simple.toml:**
```toml
[package]
name = "robotics-sim"
version = "0.1.0"

[dependencies]
physics = { version = "0.1", features = ["genesis", "isaac-lab"] }

[build]
# Python environment for Genesis
python-path = ".venv/bin/python"

# Isaac SDK path for C++ bindings
isaac-sdk-path = "/opt/isaac-sim"

[features]
default = ["genesis"]
genesis = []
isaac-lab = []
both = ["genesis", "isaac-lab"]
```

### 5.4 GPU Memory Management

#### Unified Memory Abstraction

**Simple's GPU Memory API:**
```simple
# Generic over device (CPU, GPU, TPU, etc.)
enum Device:
    CPU
    CUDA(device_id: i32)
    Vulkan(device_id: i32)
    Metal(device_id: i32)

struct GpuTensor<T, Shape>:
    device_ptr: DevicePtr
    shape: Shape
    device: Device

    fn new(shape: Shape, device: Device) -> Self:
        let size_bytes = shape.num_elements() * sizeof(T)
        let device_ptr = allocate_device_memory(device, size_bytes)
        return GpuTensor { device_ptr, shape, device }

    fn from_cpu(data: Tensor<T, Shape>, device: Device) -> Self:
        let gpu_tensor = GpuTensor::new(data.shape, device)
        copy_to_device(data.as_ptr(), gpu_tensor.device_ptr, data.size_bytes())
        return gpu_tensor

    fn to_cpu() -> Tensor<T, Shape>:
        let cpu_tensor = Tensor::new_zeroed(shape)
        copy_from_device(device_ptr, cpu_tensor.as_mut_ptr(), size_bytes())
        return cpu_tensor

    # Zero-copy view (if already on device)
    fn as_view() -> GpuTensorView<T, Shape>:
        return GpuTensorView { device_ptr, shape, device }
```

#### Integration with Physics Engines

**Genesis (via Taichi):**
```simple
# Taichi manages GPU memory internally
# We need to copy to/from Taichi tensors

fn get_genesis_state_gpu(scene: GenesisScene) -> GpuTensor<f32, [NumEnvs, StateDim]>:
    # Get from Genesis (Python) as numpy array
    let np_array = scene.get_state_numpy()

    # Check if already on GPU
    if np_array.is_cuda():
        # Get CUDA pointer from numpy
        let cuda_ptr = np_array.data_ptr()

        # Wrap as Simple GPU tensor (zero-copy)
        return GpuTensor::from_device_ptr(
            cuda_ptr,
            shape=[num_envs, state_dim],
            device=Device::CUDA(0)
        )
    else:
        # Copy from CPU to GPU
        let cpu_tensor = Tensor::from_numpy(np_array)
        return GpuTensor::from_cpu(cpu_tensor, Device::CUDA(0))
```

**Isaac Lab (PhysX Tensor API):**
```simple
# Direct access to PhysX GPU memory

fn get_isaac_joint_positions_gpu() -> GpuTensor<f32, [NumEnvs, NumJoints]>:
    # C API returns CUDA device pointer
    let device_ptr = isaac_get_joint_positions_gpu_ptr(scene_handle)

    # Wrap as Simple tensor (zero-copy, no ownership transfer)
    return GpuTensor::from_device_ptr(
        device_ptr,
        shape=[num_envs, num_joints],
        device=Device::CUDA(0)
    )
```

#### Memory Pools and Allocation

**Pre-allocated Memory for Nogc:**
```simple
@nogc
struct SimulationMemoryPool:
    # Pre-allocated GPU buffers
    state_buffer: GpuTensor<f32, [NumEnvs, StateDim]>
    action_buffer: GpuTensor<f32, [NumEnvs, ActionDim]>
    reward_buffer: GpuTensor<f32, [NumEnvs]>

    fn create(num_envs: i32, device: Device) -> Self:
        return SimulationMemoryPool(
            state_buffer=GpuTensor::new([num_envs, state_dim], device),
            action_buffer=GpuTensor::new([num_envs, action_dim], device),
            reward_buffer=GpuTensor::new([num_envs], device)
        )

    @nogc
    fn step(policy: NeuralNetwork):
        # All operations use pre-allocated buffers
        # No dynamic allocation
        policy.forward(state_buffer, mut action_buffer)
        backend.step(action_buffer, mut state_buffer, mut reward_buffer)
```

### 5.5 Batch Simulation Patterns

#### Pattern 1: Synchronous Batch

**All environments step together:**
```simple
@async @nogc
fn synchronous_batch_training(
    scene: mut BatchedSimulation,
    policy: mut NeuralNetwork,
    num_steps: i32
):
    let obs = scene.reset()  # [num_envs, obs_dim]

    for step in 0..num_steps:
        # Inference on all envs
        let actions = policy.forward(obs).await  # [num_envs, action_dim]

        # Step all envs
        obs, rewards, dones = scene.step(actions).await

        # Reset completed episodes
        if dones.any():
            let reset_ids = dones.nonzero()
            obs[reset_ids] = scene.reset(reset_ids)
```

**Pros:**
- Simple implementation
- Predictable performance
- Good GPU utilization

**Cons:**
- Wasted compute on finished episodes (until reset)

#### Pattern 2: Asynchronous Episodes

**Environments reset independently:**
```simple
@async @nogc
fn async_episode_training(
    scene: mut BatchedSimulation,
    policy: mut NeuralNetwork,
    num_episodes: i32
):
    let obs = scene.reset()
    let episode_counts = Array::zeros(num_envs)

    loop:
        let actions = policy.forward(obs).await
        obs, rewards, dones = scene.step(actions).await

        # Reset finished episodes independently
        for env_id in dones.nonzero():
            obs[env_id] = scene.reset_single(env_id)
            episode_counts[env_id] += 1

        # Stop when all envs have completed enough episodes
        if episode_counts.min() >= num_episodes:
            break
```

**Pros:**
- Better sample efficiency
- No wasted compute

**Cons:**
- More complex reset logic
- Slight overhead from selective reset

#### Pattern 3: Multi-GPU Sharding

**Shard environments across multiple GPUs:**
```simple
@async @nogc
fn multi_gpu_training(
    num_envs_per_gpu: i32,
    num_gpus: i32,
    policy: NeuralNetwork
):
    # Create actor for each GPU
    let shards = Array::new()
    for gpu_id in 0..num_gpus:
        let shard = SimulationShard::spawn_on_device(
            device=Device::CUDA(gpu_id),
            num_envs=num_envs_per_gpu,
            policy=policy.clone()
        )
        shards.push(shard)

    # Run all shards concurrently
    let handles = shards.map(|shard| shard.run_training())

    # Wait for all to complete
    for handle in handles:
        handle.await
```

**Pros:**
- Linear scaling with GPUs (up to bandwidth limits)
- Isolated failures (one GPU error doesn't crash all)

**Cons:**
- Requires parameter synchronization
- Communication overhead for distributed RL

---

## 6. Recommended Path Forward

### 6.1 Phase 1: Foundation (Weeks 1-4)

**Goals:**
- Establish FFI infrastructure
- Implement minimal viable bindings for one backend
- Validate Simple's unit types with physics APIs

**Tasks:**

1. **Python FFI Layer (Week 1-2)**
   - Integrate PyO3 into Simple's runtime
   - Create Simple↔Python object marshalling
   - Test with simple Genesis example

2. **Genesis Minimal Bindings (Week 2-3)**
   - Wrap Scene creation/destruction
   - Wrap add_entity (rigid body only)
   - Wrap step/reset
   - Extract state as Simple tensors

3. **Unit Type Integration (Week 3-4)**
   - Map Simple's #Force, #Torque, etc. to Genesis API
   - Implement conversions at FFI boundary
   - Write tests verifying type safety

**Deliverables:**
- Working Genesis scene from Simple
- Type-safe force application
- Batched simulation (100 envs)

### 6.2 Phase 2: Core Abstractions (Weeks 5-8)

**Goals:**
- Design backend-agnostic API
- Implement both Genesis and Isaac Lab backends
- Support basic RL workflows

**Tasks:**

1. **Unified API Design (Week 5)**
   - Define Scene, RigidBody, Articulation traits
   - Design observation/action managers
   - Specify backend trait

2. **Genesis Backend (Week 6)**
   - Implement full Genesis wrapper
   - Support all solvers (rigid, MPM, SPH, etc.)
   - Material system bindings

3. **Isaac Lab Backend (Week 7)**
   - C++ SDK integration (PhysX, USD)
   - Tensor API bindings
   - Zero-copy GPU access

4. **RL Environment Interface (Week 8)**
   - Gym-compatible API
   - Batched step/reset
   - Reward/termination managers

**Deliverables:**
- Two backends behind unified API
- Can switch backends with config change
- Basic RL training example

### 6.3 Phase 3: Performance Optimization (Weeks 9-12)

**Goals:**
- Maximize GPU utilization
- Minimize CPU-GPU transfers
- Achieve competitive performance

**Tasks:**

1. **GPU Memory Optimization (Week 9)**
   - Zero-copy tensor views
   - Memory pooling for nogc
   - Async memory transfers

2. **Custom Kernels (Week 10)**
   - Observation preprocessing kernels
   - Reward computation kernels
   - Compare with backend implementations

3. **Multi-GPU Support (Week 11)**
   - Actor-based sharding
   - Parameter synchronization
   - Distributed RL integration

4. **Benchmarking (Week 12)**
   - Compare with native Python implementations
   - Measure overhead of Simple layer
   - Optimize hot paths

**Deliverables:**
- <5% overhead vs. native
- Multi-GPU scaling demonstrated
- Performance report

### 6.4 Phase 4: Advanced Features (Weeks 13-16)

**Goals:**
- Support all simulation types
- Advanced sensors and rendering
- Production-ready library

**Tasks:**

1. **Soft Bodies and Fluids (Week 13)**
   - FEM/PBD bindings
   - SPH/MPM bindings
   - Coupling between solvers

2. **Sensors and Rendering (Week 14)**
   - Camera support (RGB, depth, segmentation)
   - LiDAR and point clouds
   - Ray tracing integration (Isaac Lab)

3. **Advanced RL Features (Week 15)**
   - Curriculum learning
   - Domain randomization
   - Procedural environment generation

4. **Documentation and Examples (Week 16)**
   - API documentation
   - Tutorial examples
   - Migration guides (from Genesis/Isaac Lab Python)

**Deliverables:**
- Comprehensive physics library
- Example suite (10+ scenarios)
- Public documentation

### 6.5 Success Metrics

**Performance Targets:**
- Match or exceed Genesis Python performance
- <10% overhead vs. Isaac Lab C++ API
- 1M+ FPS on 4096 envs (simple task, single A100)

**API Quality Targets:**
- 100% type-safe physics operations
- Zero-copy GPU access for all backends
- <100 LOC for basic RL environment

**Robustness Targets:**
- Comprehensive test suite (unit + integration)
- Formal verification of unit conversions
- Memory safety guarantees (no crashes from FFI)

---

## 7. Example Implementation Sketches

### 7.1 Simple Manipulation Task

**Goal:** Reach a target position with Franka Panda arm

```simple
import physics.{Scene, Articulation, Vec3}
import physics.backends.Genesis

# Environment definition
struct ReachEnv:
    scene: Scene
    robot: Articulation
    target_pos: GpuTensor<Vec3<#Length>, [NumEnvs]>

    @static
    fn create(num_envs: i32) -> Self:
        # Create scene
        let scene = Scene::builder()
            .backend(Backend::Genesis)
            .num_envs(num_envs)
            .timestep(#Duration::from_millis(10))
            .build()

        # Add ground plane
        scene.add_entity(Plane::new())

        # Add robot (auto-cloned across envs)
        let robot = scene.add_articulation(
            Articulation::from_urdf("franka_panda.urdf")
        )

        # Random target positions
        let target_pos = GpuTensor::rand(
            [num_envs],
            range=(
                Vec3::new(0.3, -0.3, 0.1).map(#Length::from_meters),
                Vec3::new(0.6, 0.3, 0.5).map(#Length::from_meters)
            )
        )

        return ReachEnv { scene, robot, target_pos }

    fn reset(env_ids: Option<Array<i32>>) -> Tensor<f32, [NumEnvs, ObsDim]>:
        # Reset joint positions
        let reset_pos = Tensor::zeros([num_envs, 7])
            .map(#Angle::from_radians)
        robot.set_joint_positions(reset_pos, env_ids)

        # Randomize targets (if specified envs)
        if let Some(ids) = env_ids:
            for id in ids:
                target_pos[id] = sample_random_target()

        return get_observation()

    fn step(actions: Tensor<f32, [NumEnvs, ActionDim]>)
        -> (Tensor<f32>, Tensor<f32>, Tensor<bool>):

        # Convert actions to joint targets
        let joint_targets = actions.map(#Angle::from_radians)
        robot.set_joint_position_targets(joint_targets)

        # Simulate
        scene.step()

        # Compute reward
        let ee_pos = robot.get_link_position("ee_link")
        let dist = (ee_pos - target_pos).norm()
        let reward = -dist.as_meters()  # Negative distance

        # Check termination
        let done = dist < #Length::from_meters(0.05)  # 5cm threshold

        return (get_observation(), reward, done)

    fn get_observation() -> Tensor<f32, [NumEnvs, ObsDim]>:
        let joint_pos = robot.get_joint_positions().map(|a| a.as_radians())
        let joint_vel = robot.get_joint_velocities().map(|v| v.as_rad_s())
        let ee_pos = robot.get_link_position("ee_link").map(|p| p.as_meters())
        let target = target_pos.map(|p| p.as_meters())

        return Tensor::concat([joint_pos, joint_vel, ee_pos, target], dim=1)
```

### 7.2 RL Training Loop

```simple
import physics.ReachEnv
import ml.{PPO, NeuralNetwork}

@async @nogc
fn train_reaching():
    # Create environment
    let env = ReachEnv::create(num_envs=4096)

    # Create policy network
    let policy = NeuralNetwork::builder()
        .layer(Linear(obs_dim=20, hidden=256))
        .layer(ReLU())
        .layer(Linear(hidden=256, out=7))
        .layer(Tanh())
        .device(Device::CUDA(0))
        .build()

    # Create RL algorithm
    let trainer = PPO::new(policy, lr=3e-4)

    # Training loop
    let obs = env.reset(None)

    for step in 0..1_000_000:
        # Get actions from policy
        let actions = policy.forward(obs).await

        # Step environment
        obs, rewards, dones = env.step(actions)

        # Store transition
        trainer.store_transition(obs, actions, rewards, dones)

        # Update policy every N steps
        if step % 2048 == 0:
            trainer.update().await
            print("Step {}: mean_reward = {:.2f}", step, rewards.mean())

        # Reset finished episodes
        if dones.any():
            let reset_ids = dones.nonzero()
            obs[reset_ids] = env.reset(Some(reset_ids))
```

### 7.3 Multi-Physics Coupling Example

**Goal:** Soft robot manipulating fluid

```simple
import physics.{Scene, SoftBody, Fluid}
import physics.backends.Genesis

fn soft_fluid_manipulation():
    # Create scene
    let scene = Scene::builder()
        .backend(Backend::Genesis)
        .num_envs(1024)
        .build()

    # Add soft robot (FEM)
    let soft_robot = scene.add_soft_body(
        SoftBody::from_mesh("soft_gripper.obj")
            .material(FEMMaterial(
                youngs_modulus=#Pressure::from_pa(1e6),
                poisson_ratio=0.45,
                density=#Density::from_kg_m3(1000.0)
            ))
    )

    # Add fluid (SPH)
    let fluid = scene.add_fluid(
        Fluid::box_region(
            center=Vec3::new(0.0, 0.0, 0.2).map(#Length::from_meters),
            size=Vec3::new(0.1, 0.1, 0.1).map(#Length::from_meters),
            particle_spacing=#Length::from_mm(2.0)
        )
        .material(SPHMaterial(
            density=#Density::from_kg_m3(1000.0),
            viscosity=#DynamicViscosity::from_pa_s(0.001)
        ))
    )

    # Simulate coupled system
    for step in 0..1000:
        # Actuate soft robot
        soft_robot.apply_pressure(
            face_group="inner_surface",
            pressure=#Pressure::from_pa(1000.0 * sin(step as f32 * 0.1))
        )

        # Genesis automatically handles FEM-SPH coupling
        scene.step()

        # Render
        scene.render("output_{:04d}.png", step)
```

---

## 8. Conclusion and Recommendations

### 8.1 Summary

Both **Genesis** and **Isaac Lab** represent state-of-the-art physics simulation platforms with complementary strengths:

**Genesis Strengths:**
- Pure Python, easier integration for prototyping
- Unified multi-physics (rigid + soft + fluid + granular)
- Exceptional performance (10-80x faster than alternatives)
- Open source and actively developed

**Isaac Lab Strengths:**
- NVIDIA ecosystem integration (PhysX, RTX, USD)
- Production-grade photorealistic rendering
- Direct GPU tensor API for zero-copy access
- Comprehensive sensor suite (cameras, LiDAR, IMU)

**Simple Language Advantages:**
1. **Type Safety:** Unit types prevent physics errors at compile time
2. **GPU Performance:** Native Vulkan/CUDA support matches backend capabilities
3. **Memory Safety:** Nogc and effect system for deterministic real-time performance
4. **Concurrency:** Actor model naturally expresses multi-GPU distributed simulation

### 8.2 Recommended Strategy

**Primary Recommendation:** **Implement both backends behind unified Simple API**

**Rationale:**
- Genesis for research and multi-physics
- Isaac Lab for production robotics with visual fidelity
- Unified API allows code reuse and backend switching

**Implementation Priority:**
1. **Start with Genesis** (simpler FFI via Python, faster initial progress)
2. **Add Isaac Lab** (C++ integration, production features)
3. **Optimize performance** (GPU memory, custom kernels)
4. **Advanced features** (multi-physics, rendering, distributed training)

### 8.3 Key Design Principles

**Type Safety First:**
- Enforce unit types for all physical quantities
- Prevent common errors (force vs. torque, angle vs. angular velocity)
- Self-documenting APIs

**Zero-Copy Where Possible:**
- Direct GPU tensor access (Isaac Lab PhysX API)
- Avoid CPU-GPU roundtrips
- Wrapper overhead <5%

**Effect System Guarantees:**
- Async for GPU kernels and I/O
- Nogc for real-time simulation loops
- Mut/immutable for safe concurrency

**Backend Abstraction:**
- Same Simple code runs on Genesis or Isaac Lab
- Configuration-driven backend selection
- Interchangeable for A/B testing

### 8.4 Potential Challenges

**Python Interop Overhead:**
- Genesis FFI requires crossing Python boundary
- Solution: Cache frequently accessed objects, batch operations
- Fallback: Direct Taichi kernel calls for hot paths

**API Surface Complexity:**
- Both engines have extensive APIs
- Solution: Phased implementation, prioritize RL workflows
- Documentation: Clear migration guides from native APIs

**Version Compatibility:**
- Both projects evolving rapidly (Genesis especially)
- Solution: Pin versions, automated testing against releases
- Community: Contribute upstream for Simple-friendly features

### 8.5 Future Opportunities

**Custom Physics Solvers in Simple:**
- Use Simple's GPU capabilities to implement custom solvers
- Contribute back to Genesis/Isaac Lab ecosystems
- Simple-native physics for specialized domains

**Formal Verification:**
- Leverage Simple's Lean 4 verification
- Prove correctness of physics equations
- Verified contact dynamics, collision detection

**Multi-Modal Learning:**
- Combine vision (Isaac Lab rendering) with physics (Genesis speed)
- Transfer learning across simulators
- Sim-to-real research opportunities

**Educational Platform:**
- Simple's readability + physics simulation
- Teaching robotics/RL with type-safe framework
- Interactive notebooks (Jupyter + Simple)

---

## Sources

### Genesis Physics Engine
- [Genesis Official Website](https://genesis-embodied-ai.github.io/)
- [Genesis Documentation](https://genesis-world.readthedocs.io/)
- [Genesis GitHub Repository](https://github.com/Genesis-Embodied-AI/Genesis)
- [DataCamp: Genesis Physics Engine Guide](https://www.datacamp.com/blog/genesis-physics-engine)
- [DataCamp: Genesis Tutorial](https://www.datacamp.com/tutorial/genesis-physics-engine-tutorial)
- [MarkTechPost: Genesis Overview](https://www.marktechpost.com/2024/12/19/meet-genesis-an-open-source-physics-ai-engine-redefining-robotics-with-ultra-fast-simulations-and-generative-4d-worlds/)

### Isaac Lab/Gym
- [NVIDIA Isaac Lab Research Paper](https://research.nvidia.com/publication/2025-09_isaac-lab-gpu-accelerated-simulation-framework-multi-modal-robot-learning)
- [Isaac Lab arXiv Paper](https://arxiv.org/html/2511.04831v1)
- [Isaac Lab GitHub Repository](https://github.com/isaac-sim/IsaacLab)
- [NVIDIA Isaac Sim Developer Page](https://developer.nvidia.com/isaac/sim)
- [NVIDIA Isaac Developer Hub](https://developer.nvidia.com/isaac)
- [Isaac Lab Official Page](https://developer.nvidia.com/isaac/lab)
- [Isaac Lab Documentation: Environment Design](https://isaac-sim.github.io/IsaacLab/main/source/setup/walkthrough/technical_env_design.html)
- [Isaac Lab Documentation: Multi-GPU Training](https://isaac-sim.github.io/IsaacLab/main/source/features/multi_gpu.html)
- [PhysX Direct GPU API Documentation](https://nvidia-omniverse.github.io/PhysX/physx/5.4.0/docs/DirectGPUAPI.html)
- [Isaac Gym Documentation: Tensor API](https://docs.robotsfan.com/isaacgym/programming/tensors.html)

### General Robotics Simulation
- [ORBIT Framework Paper](https://arxiv.org/html/2301.04195v2)
- [Project Chrono Physics Engine](https://projectchrono.org/)
- [Bullet Physics SDK GitHub](https://github.com/bulletphysics/bullet3)
- [Rapier Rust Physics Engine](https://rapier.rs/)

### Research and Comparisons
- [Isaac Gym vs Isaac Sim Forum Discussion](https://forums.developer.nvidia.com/t/isaac-gym-vs-isaac-sim/283464)
- [NVIDIA Newton Physics Engine Announcement](https://developer.nvidia.com/blog/announcing-newton-an-open-source-physics-engine-for-robotics-simulation/)
- [Computational Physics via Rust](https://cpvr.rantai.dev/)
