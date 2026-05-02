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

