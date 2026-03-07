# Vulkan GPU Backend User Guide

**Version:** 0.1.0
**Status:** MVP (Minimum Viable Product)
**Last Updated:** 2025-12-26

## Table of Contents

1. [Introduction](#introduction)
2. [Setup](#setup)
3. [Quick Start](#quick-start)
4. [Writing GPU Kernels](#writing-gpu-kernels)
5. [API Reference](#api-reference)
6. [Examples](#examples)
7. [Troubleshooting](#troubleshooting)
8. [Performance Tips](#performance-tips)
9. [Limitations](#limitations)

## Introduction

The Vulkan GPU backend enables Simple programs to execute compute kernels on GPUs using the cross-platform Vulkan API. This provides:

- **High Performance**: GPU acceleration for parallel workloads
- **Cross-Platform**: Works on Windows, Linux, macOS (via MoltenVK)
- **Automatic Fallback**: Degrades gracefully to CPU execution when GPU unavailable
- **Type Safety**: Full Simple type system support in GPU code

### When to Use the Vulkan Backend

**Good Use Cases:**
- Large parallel computations (vector operations, matrix math)
- Data-parallel algorithms (map, reduce, filter)
- Image processing and computer vision
- Scientific computing and simulations

**Not Recommended:**
- Small datasets (< 1000 elements) - CPU overhead dominates
- Irregular control flow (lots of branches)
- Tasks requiring frequent CPU-GPU data transfer

## Setup

### Prerequisites

**Required:**
- Simple compiler with `vulkan` feature enabled
- Vulkan-capable GPU and drivers
- Operating system: Linux, Windows, or macOS

**Optional:**
- Vulkan SDK (for validation and debugging)
- `spirv-val` tool (for SPIR-V validation)

### Installing Vulkan Drivers

#### Linux

**Ubuntu/Debian:**
```bash
# For NVIDIA GPUs
sudo apt install nvidia-driver-XXX vulkan-utils

# For AMD GPUs
sudo apt install mesa-vulkan-drivers vulkan-utils

# For Intel GPUs
sudo apt install intel-media-va-driver vulkan-utils

# Verify installation
vulkaninfo
```

**Arch Linux:**
```bash
# NVIDIA
sudo pacman -S nvidia vulkan-tools

# AMD
sudo pacman -S vulkan-radeon vulkan-tools

# Intel
sudo pacman -S vulkan-intel vulkan-tools
```

#### Windows

1. Install latest GPU drivers from manufacturer:
   - NVIDIA: https://www.nvidia.com/drivers
   - AMD: https://www.amd.com/support
   - Intel: https://www.intel.com/content/www/us/en/download-center/home.html

2. Vulkan runtime is typically included with drivers

3. Verify installation:
   ```powershell
   # Download Vulkan SDK or use GPU vendor tools
   # Run vulkaninfo.exe to verify
   ```

#### macOS

macOS doesn't natively support Vulkan, but you can use MoltenVK:

```bash
# Install via Homebrew
brew install molten-vk

# Verify
vulkaninfo
```

**Note:** MoltenVK translates Vulkan calls to Metal, Apple's native GPU API.

### Installing SPIR-V Tools (Optional but Recommended)

SPIR-V Tools includes `spirv-val`, which validates generated SPIR-V bytecode. This is useful for development and debugging.

#### Linux

**Ubuntu/Debian:**
```bash
sudo apt install spirv-tools

# Verify installation
spirv-val --version
```

**Arch Linux:**
```bash
sudo pacman -S spirv-tools

# Verify
spirv-val --version
```

**From Source:**
```bash
git clone https://github.com/KhronosGroup/SPIRV-Tools.git
cd SPIRV-Tools
mkdir build && cd build
cmake ..
make -j$(nproc)
sudo make install
```

#### macOS

```bash
# Via Homebrew
brew install spirv-tools

# Verify
spirv-val --version
```

#### Windows

**Option 1: Via Vulkan SDK**
- Download and install Vulkan SDK from https://vulkan.lunarg.com/
- SPIR-V Tools are included in the SDK
- Add `C:\VulkanSDK\<version>\Bin` to PATH

**Option 2: Via vcpkg**
```powershell
# Install vcpkg if not already installed
git clone https://github.com/Microsoft/vcpkg.git
cd vcpkg
.\bootstrap-vcpkg.bat

# Install SPIR-V Tools
.\vcpkg install spirv-tools:x64-windows
```

**Option 3: Download Pre-built Binaries**
- Visit https://github.com/KhronosGroup/SPIRV-Tools/releases
- Download latest Windows release
- Extract and add to PATH

**Verify Installation:**
```powershell
spirv-val --version
```

### Building Simple with Vulkan Support

```bash
# Build compiler with Vulkan feature
cargo build --release --features vulkan

# Build runtime with Vulkan feature
cargo build --release -p simple-runtime --features vulkan

# Run tests to verify
cargo test --features vulkan
```

### Verifying Installation

Create a test file `test_vulkan.spl`:

```simple
import std.gpu.vulkan

fn main():
    if vulkan.available():
        print("Vulkan is available!")
        device = vulkan.Device.create()
        print(f"Device: {device.name()}")
        device.free()
    else:
        print("Vulkan not available - will use CPU fallback")
```

Run it:
```bash
./target/release/simple test_vulkan.spl
```

## Quick Start

### Your First GPU Kernel

Let's write a simple vector addition kernel:

**File:** `vector_add.spl`

```simple
import std.gpu.vulkan as vk

# Define a GPU kernel function
# Note: This is pseudocode - actual GPU kernel syntax to be implemented
fn vector_add_kernel(a: Array[f32], b: Array[f32], result: Array[f32]):
    """
    Add two vectors element-wise on the GPU.

    Args:
        a: First input vector
        b: Second input vector
        result: Output vector
    """
    # Get global work item ID
    i = gpu_global_id(0)

    # Bounds check
    if i < a.len():
        result[i] = a[i] + b[i]

fn main():
    # Create input data
    size = 1024
    a = Array.filled(size, 1.0)
    b = Array.filled(size, 2.0)
    result = Array.filled(size, 0.0)

    # Check if Vulkan is available
    if not vk.available():
        print("Vulkan not available, using CPU")
        # CPU fallback
        for i in range(size):
            result[i] = a[i] + b[i]
        return

    # Create Vulkan device
    device = vk.Device.create()

    # Allocate GPU buffers
    gpu_a = device.alloc_buffer(size * 4)  # 4 bytes per f32
    gpu_b = device.alloc_buffer(size * 4)
    gpu_result = device.alloc_buffer(size * 4)

    # Upload data to GPU
    gpu_a.upload(a.as_bytes())
    gpu_b.upload(b.as_bytes())

    # Compile kernel (SPIR-V generated automatically)
    kernel = device.compile_kernel(vector_add_kernel)

    # Execute kernel
    kernel.launch(
        buffers=[gpu_a, gpu_b, gpu_result],
        global_size=size,
        local_size=256  # Work group size
    )

    # Wait for completion
    device.sync()

    # Download results
    result_bytes = gpu_result.download()
    result = Array.from_bytes(result_bytes, dtype=f32)

    # Verify results
    print(f"Result[0] = {result[0]} (expected 3.0)")
    print(f"Result[100] = {result[100]} (expected 3.0)")

    # Cleanup
    kernel.free()
    gpu_a.free()
    gpu_b.free()
    gpu_result.free()
    device.free()
```

### Understanding the Code

**1. Kernel Function:**
```simple
fn vector_add_kernel(a: Array[f32], b: Array[f32], result: Array[f32]):
    i = gpu_global_id(0)  # Get work item index
    if i < a.len():
        result[i] = a[i] + b[i]
```
- Runs on GPU
- Each work item processes one element
- `gpu_global_id(0)` gets the unique index for this work item

**2. Device Setup:**
```simple
device = vk.Device.create()  # Create GPU device
gpu_a = device.alloc_buffer(size * 4)  # Allocate GPU memory
```

**3. Data Transfer:**
```simple
gpu_a.upload(a.as_bytes())  # CPU → GPU
result_bytes = gpu_result.download()  # GPU → CPU
```

**4. Kernel Execution:**
```simple
kernel.launch(
    buffers=[gpu_a, gpu_b, gpu_result],
    global_size=1024,  # Total work items
    local_size=256      # Work items per group
)
```

## Writing GPU Kernels

### GPU Intrinsics

Simple provides several GPU intrinsic functions:

**Work Item Identification:**
```simple
gpu_global_id(dim: u32) -> u64      # Global work item ID
gpu_local_id(dim: u32) -> u64       # Local work item ID within group
gpu_group_id(dim: u32) -> u64       # Work group ID
gpu_global_size(dim: u32) -> u64    # Total work items in dimension
gpu_local_size(dim: u32) -> u64     # Work group size
```

**Synchronization:**
```simple
gpu_barrier()                        # Synchronize all work items in group
```

**Atomic Operations:**
```simple
gpu_atomic_add(addr: *mut i32, value: i32) -> i32
gpu_atomic_sub(addr: *mut i32, value: i32) -> i32
gpu_atomic_exchange(addr: *mut i32, value: i32) -> i32
gpu_atomic_compare_exchange(addr: *mut i32, expected: i32, value: i32) -> i32
```

### Example: Matrix Multiplication

```simple
fn matmul_kernel(
    a: Array[f32],      # M x K
    b: Array[f32],      # K x N
    c: Array[f32],      # M x N
    M: u32,
    N: u32,
    K: u32
):
    # Get 2D work item position
    row = gpu_global_id(0)
    col = gpu_global_id(1)

    if row >= M or col >= N:
        return

    # Compute dot product
    sum = 0.0
    for k in range(K):
        a_idx = row * K + k
        b_idx = k * N + col
        sum += a[a_idx] * b[b_idx]

    # Write result
    c_idx = row * N + col
    c[c_idx] = sum
```

Launch with 2D work groups:
```simple
kernel.launch_2d(
    buffers=[gpu_a, gpu_b, gpu_c, M, N, K],
    global_size=(M, N),
    local_size=(16, 16)
)
```

### Example: Reduction (Sum)

```simple
fn reduce_sum_kernel(
    input: Array[f32],
    output: Array[f32],
    n: u32
):
    # Shared memory for partial sums (pseudo-syntax)
    shared partial_sums: Array[f32, 256]

    tid = gpu_local_id(0)
    gid = gpu_global_id(0)

    # Load data into shared memory
    if gid < n:
        partial_sums[tid] = input[gid]
    else:
        partial_sums[tid] = 0.0

    gpu_barrier()

    # Parallel reduction in shared memory
    stride = 128
    while stride > 0:
        if tid < stride:
            partial_sums[tid] += partial_sums[tid + stride]
        gpu_barrier()
        stride /= 2

    # Write result
    if tid == 0:
        output[gpu_group_id(0)] = partial_sums[0]
```

## API Reference

### Device Management

**`vulkan.available() -> bool`**
- Returns `true` if Vulkan is available on the system
- Check this before using GPU features

**`Device.create() -> Device`**
- Creates a Vulkan device
- Automatically selects the best available GPU
- Throws error if Vulkan unavailable

**`device.free()`**
- Releases GPU device
- Must be called when done with device

**`device.sync()`**
- Waits for all GPU operations to complete
- Blocks until GPU is idle

### Buffer Management

**`device.alloc_buffer(size: u64) -> Buffer`**
- Allocates GPU memory
- Size in bytes
- Returns buffer handle

**`buffer.free()`**
- Releases GPU memory
- Must be called when done with buffer

**`buffer.upload(data: bytes)`**
- Uploads data from CPU to GPU
- Data size must match buffer size

**`buffer.download() -> bytes`**
- Downloads data from GPU to CPU
- Returns byte array

### Kernel Management

**`device.compile_kernel(fn) -> Kernel`**
- Compiles a Simple function to SPIR-V
- Returns executable kernel
- Compilation happens at runtime

**`kernel.free()`**
- Releases compiled kernel
- Must be called when done

**`kernel.launch(buffers, global_size, local_size=256)`**
- Executes kernel on GPU
- `buffers`: List of GPU buffers
- `global_size`: Total number of work items
- `local_size`: Work items per group (default: 256)

**`kernel.launch_2d(buffers, global_size, local_size)`**
- Executes kernel with 2D work groups
- `global_size`: Tuple (width, height)
- `local_size`: Tuple (width, height)

**`kernel.launch_3d(buffers, global_size, local_size)`**
- Executes kernel with 3D work groups
- `global_size`: Tuple (x, y, z)
- `local_size`: Tuple (x, y, z)

## Examples

### Example 1: Vector Scaling

Multiply every element by a constant:

```simple
fn scale_kernel(input: Array[f32], output: Array[f32], scale: f32):
    i = gpu_global_id(0)
    if i < input.len():
        output[i] = input[i] * scale

fn main():
    data = [1.0, 2.0, 3.0, 4.0, 5.0]
    result = [0.0; data.len()]

    device = vulkan.Device.create()
    gpu_in = device.alloc_buffer(data.len() * 4)
    gpu_out = device.alloc_buffer(data.len() * 4)

    gpu_in.upload(data.as_bytes())

    kernel = device.compile_kernel(scale_kernel)
    kernel.launch([gpu_in, gpu_out, 2.0], global_size=data.len())

    device.sync()
    result = Array.from_bytes(gpu_out.download(), f32)

    print(result)  # [2.0, 4.0, 6.0, 8.0, 10.0]
```

### Example 2: Element-wise Maximum

```simple
fn max_kernel(a: Array[f32], b: Array[f32], result: Array[f32]):
    i = gpu_global_id(0)
    if i < a.len():
        result[i] = max(a[i], b[i])
```

### Example 3: Image Blur (2D)

```simple
fn blur_kernel(
    input: Array[u8],   # Input image
    output: Array[u8],  # Output image
    width: u32,
    height: u32
):
    x = gpu_global_id(0)
    y = gpu_global_id(1)

    if x >= width or y >= height:
        return

    # 3x3 box blur
    sum = 0
    count = 0

    for dy in [-1, 0, 1]:
        for dx in [-1, 0, 1]:
            nx = x + dx
            ny = y + dy

            if 0 <= nx < width and 0 <= ny < height:
                idx = ny * width + nx
                sum += input[idx]
                count += 1

    idx = y * width + x
    output[idx] = sum / count
```

## Troubleshooting

### Common Issues

**Issue: "Vulkan not available"**

**Cause:** Missing drivers or Vulkan runtime

**Solution:**
1. Verify GPU supports Vulkan: `vulkaninfo`
2. Update GPU drivers to latest version
3. On Linux, install mesa-vulkan-drivers or vendor drivers
4. On macOS, install MoltenVK

---

**Issue: "Failed to create device"**

**Cause:** All GPUs in use or insufficient permissions

**Solution:**
1. Close other GPU-intensive applications
2. Check GPU is not overheating
3. On Linux, ensure user in `video` group: `sudo usermod -a -G video $USER`

---

**Issue: "Buffer allocation failed"**

**Cause:** Out of GPU memory

**Solution:**
1. Reduce buffer sizes
2. Free unused buffers
3. Process data in batches
4. Use smaller work group sizes

---

**Issue: Kernel runs but produces wrong results**

**Cause:** Race conditions or out-of-bounds access

**Solution:**
1. Add bounds checks: `if i < array.len()`
2. Use `gpu_barrier()` for synchronization
3. Verify work group sizes are correct
4. Check buffer sizes match data sizes

---

**Issue: Performance is slower than CPU**

**Cause:** Small dataset or too much data transfer

**Solution:**
1. Only use GPU for datasets > 10,000 elements
2. Minimize CPU↔GPU transfers
3. Increase work group size (256-512)
4. Process multiple operations in one kernel

## Performance Tips

### 1. Minimize Data Transfer

**Bad:**
```simple
for i in range(1000):
    gpu_buffer.upload(data)
    kernel.launch(...)
    result = gpu_buffer.download()
```

**Good:**
```simple
gpu_buffer.upload(data)
for i in range(1000):
    kernel.launch(...)
device.sync()
result = gpu_buffer.download()
```

### 2. Use Appropriate Work Group Sizes

- **Too small** (< 64): Poor GPU utilization
- **Too large** (> 512): May exceed limits
- **Recommended**: 256 for 1D, 16x16 for 2D

### 3. Coalesce Memory Access

**Bad:**
```simple
# Strided access - slow
for i in range(n):
    result[i] = input[i * stride]
```

**Good:**
```simple
# Sequential access - fast
for i in range(n):
    result[i] = input[i]
```

### 4. Use Shared Memory for Reused Data

```simple
shared tile: Array[f32, 256]

# Load into shared memory once
tile[tid] = input[gid]
gpu_barrier()

# Reuse many times
for k in range(10):
    sum += tile[tid] * k
```

### 5. Avoid Divergent Branches

**Bad:**
```simple
if input[i] > 0:
    # Long computation
else:
    # Different long computation
```

**Good:**
```simple
# Compute both paths, select result
result_a = compute_path_a(input[i])
result_b = compute_path_b(input[i])
result[i] = input[i] > 0 ? result_a : result_b
```

## Limitations

### Current MVP Limitations

1. **No Automatic Kernel Detection**
   - Must manually specify which functions are GPU kernels
   - Syntax: TBD (e.g., `#[gpu]` attribute)

2. **Single Device Only**
   - Can only use one GPU at a time
   - Multi-GPU support planned for future

3. **No Pipeline Caching**
   - Kernels recompiled every run
   - Performance impact on startup

4. **Limited Type Support**
   - Primitive types: i32, i64, u32, u64, f32, f64
   - Arrays of primitives
   - No structs or complex types yet

5. **No Shared Memory Syntax**
   - Must use workarounds
   - Proper syntax planned for future

### Platform-Specific Notes

**macOS (MoltenVK):**
- Some Vulkan features may not be available
- Performance may be lower than native Metal
- Validation layers may not work

**Linux:**
- Best performance on NVIDIA and AMD
- Intel GPUs supported but slower

**Windows:**
- Excellent support on all vendors
- Validation layers work well

## Next Steps

- Read the [Architecture Documentation](../architecture/vulkan_backend.md) for implementation details
- Check out more examples in `examples/gpu/vulkan/`
- Learn about [SPIR-V generation](../codegen/vulkan_backend.md)
- Explore the [Vulkan Runtime API](../api/vulkan_runtime.md)

## Support

- **Issues:** https://github.com/simple-lang/simple/issues
- **Discussions:** https://github.com/simple-lang/simple/discussions
- **Documentation:** https://simple-lang.org/docs/gpu

## References

- Vulkan Documentation: https://www.vulkan.org/
- Vulkan Tutorial: https://vulkan-tutorial.com/
- SPIR-V Specification: https://www.khronos.org/spir/
- MoltenVK (macOS): https://github.com/KhronosGroup/MoltenVK
