# 🎯 Part 47: Hardware Scheduling
**Goal**: Understand GPU hardware scheduling mechanics, analyze occupancy limiting factors, and apply scheduling-aware kernel design patterns to maximize SM utilization.

## Project Structure
```
47.Hardware_Scheduling/
├── README.md
├── CMakeLists.txt
├── doxygen/
│   ├── Doxyfile.in
│   └── mainpage.md
├── src/
│   ├── CMakeLists.txt
│   ├── host/
│   │   └── occupancy_calculator.cpp    # OccupancyCalculator, OccupancyResult
│   └── kernels/
│       └── scheduling_kernels.cu       # Scheduling demonstration kernels
└── test/
    ├── CMakeLists.txt
    └── unit/
        └── test_scheduling.cu          # GpuTest-based tests for all kernels
```

## Quick Navigation
- [47.1 Occupancy Analysis](#471-occupancy-analysis)
- [47.2 Scheduling Kernels](#472-scheduling-kernels)
- [47.3 Build & Run](#473-build--run)
- [47.4 Summary](#474-summary)

---

## **47.1 Occupancy Analysis**
Occupancy measures how effectively an SM's resources are utilized by active warps relative to the hardware maximum. Higher occupancy generally helps hide memory latency, though it is not always the sole determinant of performance.

### **47.1.1 OccupancyResult**
The `OccupancyResult` struct captures the outcome of an occupancy calculation, including the bottleneck resource that limits the number of concurrent blocks.

```cpp
// src/host/occupancy_calculator.cpp:8-14 - Occupancy analysis output
struct OccupancyResult {
    int blocksPerSM;
    int activeWarps;
    int activeThreads;
    float occupancyPercent;
    int limitingFactor;  // 0=threads, 1=blocks, 2=sharedMem, 3=registers
};
```

**Key Points**:
- `limitingFactor` identifies which hardware resource is the bottleneck
- `occupancyPercent` is calculated as `activeThreads / maxThreadsPerMultiProcessor * 100`

### **47.1.2 OccupancyCalculator**
The `OccupancyCalculator` struct wraps `cudaDeviceProp` to provide occupancy analysis for a given kernel configuration. It queries the device at construction time and exposes three core methods.

```cpp
// src/host/occupancy_calculator.cpp:16-23 - Constructor queries device properties
OccupancyCalculator(int device = 0) : deviceId(device) {
    cudaGetDeviceProperties(&deviceProps, device);
}
```

**`printDeviceInfo()`** prints SM count, max threads/blocks per SM, warp size, shared memory, and register limits for the selected device.
**Source**: `src/host/occupancy_calculator.cpp:24-34`

**`calculateOccupancy(blockSize, sharedMemPerBlock, regsPerThread)`** computes the maximum concurrent blocks per SM by evaluating four independent resource limits and selecting the minimum.

```cpp
// src/host/occupancy_calculator.cpp:36-70 - Core occupancy calculation
OccupancyResult calculateOccupancy(int blockSize, int sharedMemPerBlock, int regsPerThread) const {
    // Calculate maximum blocks limited by each resource
    int maxBlocksByThreads = deviceProps.maxThreadsPerMultiProcessor / blockSize;
    int maxBlocksByBlocks = deviceProps.maxBlocksPerMultiProcessor;
    int maxBlocksBySharedMem = (sharedMemPerBlock > 0) ?
        static_cast<int>(deviceProps.sharedMemPerMultiprocessor / sharedMemPerBlock) : INT_MAX;
    int maxBlocksByRegs = (regsPerThread > 0) ?
        deviceProps.regsPerMultiprocessor / (blockSize * regsPerThread) : INT_MAX;

    // Find the limiting factor (minimum of all four limits)
    // ...
}
```

**Key Points**:
- Four resource limits are evaluated independently: threads, blocks, shared memory, and registers
- The smallest value becomes `blocksPerSM` and the corresponding resource is flagged as `limitingFactor`

### **47.1.3 Occupancy Limiting Factors**
The `printOccupancyAnalysis()` method displays all four resource limits alongside the active bottleneck, making it easy to identify which resource to optimize.

```cpp
// src/host/occupancy_calculator.cpp:72-100 - Detailed occupancy diagnostics
void printOccupancyAnalysis(int blockSize, int sharedMemPerBlock, int regsPerThread) const {
    // ...
    printf("    By threads: %d blocks%s\n", maxBlocksByThreads,
           result.limitingFactor == 0 ? " [LIMITING]" : "");
    printf("    By blocks: %d blocks%s\n", maxBlocksByBlocks,
           result.limitingFactor == 1 ? " [LIMITING]" : "");
    printf("    By shared memory: %d blocks%s\n", maxBlocksBySharedMem,
           result.limitingFactor == 2 ? " [LIMITING]" : "");
    printf("    By registers: %d blocks%s\n", maxBlocksByRegs,
           result.limitingFactor == 3 ? " [LIMITING]" : "");
}
```

**Key Points**:
- Thread limit: `maxThreadsPerMultiProcessor / blockSize`
- Block limit: `maxBlocksPerMultiProcessor` (hardware-fixed, architecture-dependent)
- Shared memory limit: `sharedMemPerMultiprocessor / sharedMemPerBlock`
- Register limit: `regsPerMultiprocessor / (blockSize * regsPerThread)`

### **47.1.4 Optimal Block Size Selection**
The `getOptimalBlockSize()` method sweeps common block sizes (32 through 1024) and returns the one yielding the highest theoretical occupancy for a given shared memory footprint.

```cpp
// src/host/occupancy_calculator.cpp:102-119 - Brute-force optimal block size search
int getOptimalBlockSize(size_t sharedMemPerBlock) const {
    int sizes[] = {32, 64, 96, 128, 160, 192, 224, 256, 288, 320,
                   352, 384, 416, 448, 480, 512, 768, 1024};
    int bestSize = 256;
    float bestOccupancy = 0.0f;

    for (int size : sizes) {
        if (size > deviceProps.maxThreadsPerBlock) break;
        OccupancyResult result = calculateOccupancy(size, sharedMemPerBlock, 0);
        if (result.occupancyPercent > bestOccupancy) {
            bestOccupancy = result.occupancyPercent;
            bestSize = size;
        }
    }
    return bestSize;
}
```

**Key Points**:
- Only tests multiples of 32 (warp-aligned sizes) for efficient scheduling
- Defaults to 256 if no better size is found
- Does not account for register usage; pass `regsPerThread` via `calculateOccupancy()` for manual tuning

---

## **47.2 Scheduling Kernels**
This section demonstrates how different kernel resource profiles affect hardware scheduling. Each kernel isolates a specific resource dimension so its impact on occupancy and warp scheduling can be observed independently.

### **47.2.1 Low Resource Kernel**
The simplest kernel uses minimal registers and no shared memory, achieving the highest possible occupancy on any device.

```cpp
// src/kernels/scheduling_kernels.cu:6-11 - Minimal resource usage
__global__ void low_resource_kernel(float* output, const float* input, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        output[idx] = input[idx] * 2.0f;
    }
}
```

**Key Points**:
- Near-zero register pressure allows maximum blocks per SM
- Serves as an occupancy baseline for comparison with resource-heavy kernels
- Tested across block sizes 64, 128, 256, and 512 in `DifferentBlockSizesWork`

**Source**: `src/kernels/scheduling_kernels.cu:6-11`

### **47.2.2 Register Pressure**
The `high_register_kernel` deliberately uses many local variables to increase per-thread register consumption, which reduces the number of concurrent blocks an SM can host.

```cpp
// src/kernels/scheduling_kernels.cu:14-31 - Heavy register usage
__global__ void high_register_kernel(float* output, const float* input, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        float r0 = input[idx];
        float r1 = r0 * 1.1f;
        float r2 = r1 * 1.2f;
        // ... r3 through r9
        output[idx] = r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9;
    }
}
```

**Key Points**:
- 10+ live float variables force the compiler to allocate more registers per thread
- Occupancy impact depends on the architecture's register file size (`regsPerMultiprocessor`)
- Use `--ptxas-options=-v` during compilation to see actual register counts

**Source**: `src/kernels/scheduling_kernels.cu:14-31`

### **47.2.3 Shared Memory Impact**
The `high_shared_mem_kernel` template parameterizes shared memory size so the same kernel can be tested with different footprints (512, 1024, 2048 floats).

```cpp
// src/kernels/scheduling_kernels.cu:34-55 - Template-parameterized shared memory
template<int SHARED_SIZE>
__global__ void high_shared_mem_kernel(float* output, const float* input, int n) {
    __shared__ float smem[SHARED_SIZE];

    int tid = threadIdx.x;
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    if (tid < SHARED_SIZE && idx < n) {
        smem[tid] = input[idx];
    }
    __syncthreads();

    if (idx < n) {
        float sum = 0.0f;
        for (int i = 0; i < SHARED_SIZE && i < blockDim.x; i++) {
            sum += smem[i];
        }
        output[idx] = sum / SHARED_SIZE;
    }
}
```

**Key Points**:
- `SHARED_SIZE=512` allocates 2 KB, `SHARED_SIZE=2048` allocates 8 KB per block
- Larger shared memory reduces `blocksPerSM` via the shared memory limit
- Three explicit instantiations provided at line 93-95 for 512, 1024, and 2048

**Source**: `src/kernels/scheduling_kernels.cu:34-55`, instantiations at lines 93-95

### **47.2.4 Grid-Stride Loop**
The `grid_stride_kernel` processes arbitrarily large datasets using a fixed grid size by having each thread iterate through multiple elements separated by the total grid stride.

```cpp
// src/kernels/scheduling_kernels.cu:66-73 - Grid-stride loop pattern
__global__ void grid_stride_kernel(float* output, const float* input, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    int stride = blockDim.x * gridDim.x;

    for (int i = idx; i < n; i += stride) {
        output[i] = sqrtf(input[i]) + sinf(input[i]);
    }
}
```

**Key Points**:
- Decouples grid dimensions from problem size: the grid can be tuned for occupancy independently
- Enables launching exactly the number of blocks that saturate the device (e.g., `SMs * blocksPerSM`)
- Tested with `N=10000` elements but only 32 blocks of 256 threads in `GridStrideKernelWorks`

**Source**: `src/kernels/scheduling_kernels.cu:66-73`

### **47.2.5 Warp-Level Scheduling**
The `warp_scheduling_kernel` demonstrates intra-warp communication using shuffle instructions, which execute at the warp scheduler level without shared memory.

```cpp
// src/kernels/scheduling_kernels.cu:76-90 - Warp shuffle operations
__global__ void warp_scheduling_kernel(int* output, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    int warpId = threadIdx.x / 32;
    int laneId = threadIdx.x % 32;

    if (idx < n) {
        int value = warpId * 1000 + laneId;

        // Warp-level operations
        value += __shfl_xor_sync(0xffffffff, value, 1);
        value += __shfl_xor_sync(0xffffffff, value, 2);

        output[idx] = value;
    }
}
```

**Key Points**:
- `__shfl_xor_sync` exchanges values between lane pairs within a warp without shared memory
- `0xffffffff` mask indicates all 32 lanes participate in the shuffle
- XOR with mask `1` swaps adjacent lanes (0<->1, 2<->3, ...), XOR with `2` swaps lanes offset by 2
- Warp-level primitives bypass shared memory entirely, avoiding bank conflicts and `__syncthreads()` overhead

**Source**: `src/kernels/scheduling_kernels.cu:76-90`

---

## **47.3 Build & Run**
This section describes how to build the module and run tests.

```bash
# Build from the repository root (assuming build/ directory exists)
cd build
cmake .. -G Ninja
ninja 47_Hardware_Scheduling_test

# Run all tests
./40.cuda_advanced/47.Hardware_Scheduling/47_Hardware_Scheduling_test

# Run a specific test
./40.cuda_advanced/47.Hardware_Scheduling/47_Hardware_Scheduling_test --gtest_filter="SchedulingTest.CalculateOccupancyBasic"

# Profile kernel occupancy with NVIDIA Nsight Compute
ncu --metrics sm__warps_active.avg.pct_of_peak_sustained_active \
    ./40.cuda_advanced/47.Hardware_Scheduling/47_Hardware_Scheduling_test --gtest_filter="SchedulingTest.LowResourceKernelWorks"

# Check register usage at compile time
ninja 47_Hardware_Scheduling_test 2>&1 | grep -i "register"

# Generate Doxygen documentation
ninja doxygen_47_Hardware_Scheduling
```

---

## **47.4 Summary**
This section recaps the core concepts, common pitfalls, and pointers for further study.

- **Key Takeaways**:
  - Occupancy is determined by the most constrained resource among threads, blocks, shared memory, and registers per SM
  - Register pressure from many live variables can silently reduce occupancy; use `--ptxas-options=-v` to inspect
  - Shared memory allocation is per-block; larger allocations reduce the number of concurrent blocks on an SM
  - Grid-stride loops decouple problem size from grid configuration, enabling occupancy-optimal launches
  - Warp shuffle instructions (`__shfl_xor_sync`) provide fast intra-warp communication without shared memory

- **Common Errors**:

  | Error | Cause | Solution |
  |-------|-------|----------|
  | Low occupancy despite small block size | High register or shared memory usage per block | Profile with `ncu` and reduce resource footprint |
  | Grid-stride kernel produces wrong results | Missing or incorrect stride calculation | Ensure `stride = blockDim.x * gridDim.x` |
  | `__shfl_xor_sync` returns garbage | Incorrect participation mask or divergent lanes | Use `0xffffffff` for full-warp participation, ensure all lanes reach the shuffle |
  | Block size not warp-aligned | Choosing block sizes that are not multiples of 32 | Always use multiples of 32 for block dimensions |
  | Kernel launch failure with large shared memory | Shared memory request exceeds SM limit | Reduce `SHARED_SIZE` or use `cudaFuncSetAttribute` for extended shared memory |

- **Next Steps**: [48.Tile_Based_Programming](../48.Tile_Based_Programming/README.md)

- **References**:
  - [CUDA C++ Programming Guide -- Hardware Implementation](https://docs.nvidia.com/cuda/cuda-c-programming-guide/index.html#hardware-implementation)
  - [CUDA Occupancy Calculator](https://docs.nvidia.com/cuda/cuda-occupancy-calculator/index.html)
  - [NVIDIA Nsight Compute Documentation](https://docs.nvidia.com/nsight-compute/)
  - [CUDA Warp-Level Primitives](https://docs.nvidia.com/cuda/cuda-c-programming-guide/index.html#warp-shuffle-functions)
