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

