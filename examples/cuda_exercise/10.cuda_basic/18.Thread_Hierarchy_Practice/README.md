# 🔀 Part 18: Thread Hierarchy Practice

**Goal**: Master CUDA thread hierarchy through advanced tiling strategies, warp optimization, and occupancy tuning.

## Project Structure
```
18.Thread_Hierarchy_Practice/
├── README.md                        - This documentation
├── CMakeLists.txt                   - Build configuration
├── src/                             - Source implementations
│   ├── kernels/                     - Core CUDA kernels (reusable across parts)
│   │   ├── matrix_multiply.cu       - Matrix multiplication evolution
│   │   ├── vector_add_2d.h         - 2D vector addition declarations
│   │   └── vector_add_2d.cu        - 2D grid/block configurations
│   └── part_specific/               - Module-specific code
│       ├── thread_operations.cu     - Thread hierarchy demonstrations
│       └── thread_hierarchy_demo.cu - Complete demonstration program
└── test/                            - Test files
    └── unit/                        - Unit tests
        ├── kernels/                 - Kernel tests (reusable across parts)
        │   ├── test_matrix_multiply.cu    - Matrix multiplication tests
        │   └── test_vector_add_2d.cu      - 2D vector addition tests
        └── part_specific/           - Module-specific tests
            ├── test_thread_operations.cu  - Thread operation tests
            └── test_thread_hierarchy_demo.cu - Comprehensive integration tests
```

---

## **18.1 Overview**

The CUDA thread hierarchy is fundamental to GPU performance. This section explores:
- Thread organization (threads, warps, blocks, grids)
- Tiling strategies and tile size selection
- Warp-level optimizations
- Occupancy analysis and tuning
- Thread coarsening techniques
- Avoiding warp divergence

---

## **18.2 Thread Hierarchy Components**

Understanding the CUDA thread hierarchy is essential for effective parallel programming. Each level of the hierarchy serves a specific purpose with different synchronization and memory access capabilities.

### **Visual Thread Hierarchy**

```
                    GRID (All Blocks)
                    Kernel Launch Scope
                    ┌─────────────────────────────────────────┐
                    │                                         │
                    │  Global Memory Access (All Threads)     │
                    │  Synchronization: Kernel Completion     │
                    │                                         │
                    └─────────────────────────────────────────┘
                              ▲         ▲         ▲
                              │         │         │
        ┌─────────────────────┼─────────┼─────────┼──────────────┐
        │                     │         │         │              │
        │                Block(0,0)  Block(1,0)  Block(2,0) ...  │
        │                     │         │         │              │
        └─────────────────────┼─────────┼─────────┼──────────────┘
                              │
                    ┌─────────▼─────────────────────────────┐
                    │     BLOCK (Thread Block)              │
                    │     Max: 1024 threads                 │
                    │     Shared Memory Access              │
                    │     Synchronization: __syncthreads()  │
                    │                                       │
                    │  ┌──────────┬──────────┬──────────┐  │
                    │  │  Warp 0  │  Warp 1  │  Warp 2  │  │
                    │  │ (32 thr) │ (32 thr) │ (32 thr) │  │
                    │  └──────────┴──────────┴──────────┘  │
                    │         ...                          │
                    └──────────────────────────────────────┘
                              │
                    ┌─────────▼─────────────────────────────┐
                    │       WARP (32 Threads)               │
                    │       SIMT Execution Unit             │
                    │       Implicit Synchronization        │
                    │       Shuffle Instructions            │
                    │                                       │
                    │  T0  T1  T2  ... T30  T31            │
                    │  │   │   │       │    │              │
                    │  ▼   ▼   ▼       ▼    ▼              │
                    └──────────────────────────────────────┘
                              │
                    ┌─────────▼─────────────────────────────┐
                    │         THREAD                        │
                    │         Individual Work Unit          │
                    │         Register Memory               │
                    │         Local Memory (Spills)         │
                    │                                       │
                    │    threadIdx.x, threadIdx.y, ...      │
                    │    blockIdx.x, blockIdx.y, ...        │
                    └───────────────────────────────────────┘

Example: 2D Grid of 2D Blocks
=============================
Grid: dim3(2, 2)        // 2x2 = 4 blocks
Block: dim3(8, 8)       // 8x8 = 64 threads per block
Total: 4 * 64 = 256 threads

Block Layout in Grid:
┌─────────┬─────────┐
│ Blk(0,0)│ Blk(1,0)│
├─────────┼─────────┤
│ Blk(0,1)│ Blk(1,1)│
└─────────┴─────────┘

Thread Layout in Each Block:
Thread(0,0) ... Thread(7,0)
    ...           ...
Thread(0,7) ... Thread(7,7)

Warps per Block: 64 threads / 32 = 2 warps
- Warp 0: Threads 0-31 (first 4 rows)
- Warp 1: Threads 32-63 (last 4 rows)
```

### **Hierarchy Levels**

| Level | Size | Scope | Synchronization | Memory Access |
|-------|------|-------|------------------|---------------|
| **Thread** | 1 | Individual | N/A | Registers, Local |
| **Warp** | 32 threads | SIMT unit | Implicit | Shared via shuffle |
| **Block** | ≤1024 threads | Cooperative group | `__syncthreads()` | Shared memory |
| **Grid** | All blocks | Kernel launch | Kernel completion | Global memory |

### **Hardware Limits (Typical)**
```
Max threads per block: 1024
Max thread dimensions: (1024, 1024, 64)
Max grid dimensions: (2³¹-1, 65535, 65535)
Warp size: 32 (fixed)
Max warps per SM: 64
Max blocks per SM: 32
```

---

## **18.3 Tiling Strategies**

Tiling divides large problems into smaller blocks that fit in shared memory, dramatically improving memory bandwidth utilization. Different tiling strategies offer trade-offs between occupancy, memory usage, and computational efficiency.

### **18.3.1 Square Tiles**

Square tiles provide a balanced approach for matrix operations, where both dimensions use the same tile size. This implementation is found in `src/kernels/matrix_multiply.cu`:

```cpp
// matrix_multiply.cu - Square tile implementation
template<int TILE_SIZE>
__global__ void matmul_tiled_basic(const float* A, const float* B, float* C, int N) {
    __shared__ float As[TILE_SIZE][TILE_SIZE];
    __shared__ float Bs[TILE_SIZE][TILE_SIZE];

    int row = blockIdx.y * TILE_SIZE + threadIdx.y;
    int col = blockIdx.x * TILE_SIZE + threadIdx.x;
    float sum = 0.0f;

    // Process tiles
    for (int tile = 0; tile < (N + TILE_SIZE - 1) / TILE_SIZE; tile++) {
        // Collaborative load into shared memory
        As[threadIdx.y][threadIdx.x] = A[row * N + tile * TILE_SIZE + threadIdx.x];
        Bs[threadIdx.y][threadIdx.x] = B[(tile * TILE_SIZE + threadIdx.y) * N + col];
        __syncthreads();

        // Compute partial results
        for (int k = 0; k < TILE_SIZE; k++) {
            sum += As[threadIdx.y][k] * Bs[k][threadIdx.x];
        }
        __syncthreads();
    }

    if (row < N && col < N) {
        C[row * N + col] = sum;
    }
}
```

**Source:** `src/kernels/matrix_multiply.cu:30-60`

**Tile Size Selection:**
- **8x8**: 64 threads/block - Low occupancy, good for small problems
- **16x16**: 256 threads/block - Balanced choice
- **32x32**: 1024 threads/block - Maximum threads, may limit occupancy

### **18.3.2 Rectangular Tiles**

Rectangular tiles use different dimensions for rows and columns, allowing better adaptation to non-square matrices and specific hardware constraints. This approach can optimize memory coalescing for asymmetric access patterns.

```cpp
// matrix_multiply.cu - Rectangular tile implementation
template<int TILE_Y, int TILE_X>
__global__ void matmul_rectangular_tiles(const float* A, const float* B,
                                         float* C, int N) {
    __shared__ float As[TILE_Y][TILE_X];
    __shared__ float Bs[TILE_Y][TILE_X];

    // Threads map to different aspect ratios
    int row = blockIdx.y * TILE_Y + threadIdx.y;
    int col = blockIdx.x * TILE_X + threadIdx.x;

    // Better for non-square matrices and specific memory access patterns
}
```

**Source:** `src/kernels/matrix_multiply.cu:80-115`

**Benefits:**
- Better thread utilization for non-square problems
- Can optimize for specific memory access patterns
- Flexible work distribution

### **18.3.3 Thread Coarsening**

Thread coarsening assigns multiple output elements to each thread, reducing the total thread count while increasing work per thread. This technique improves instruction-level parallelism and reduces synchronization overhead.

```cpp
// matrix_multiply.cu - Thread coarsening implementation
template<int COARSE_FACTOR>
__global__ void matmul_coarsened(const float* A, const float* B,
                                 float* C, int N) {
    const int TILE_SIZE = 32;
    __shared__ float As[TILE_SIZE][TILE_SIZE];
    __shared__ float Bs[TILE_SIZE][TILE_SIZE];

    // Each thread computes COARSE_FACTOR x COARSE_FACTOR elements
    float sum[COARSE_FACTOR][COARSE_FACTOR] = {0.0f};

    int baseRow = blockIdx.y * TILE_SIZE + threadIdx.y * COARSE_FACTOR;
    int baseCol = blockIdx.x * TILE_SIZE + threadIdx.x * COARSE_FACTOR;

    // Process tiles with coarsened computation
    for (int tile = 0; tile < (N + TILE_SIZE - 1) / TILE_SIZE; tile++) {
        // Load tiles collaboratively
        // Each thread computes multiple outputs, improving ILP
    }
}
```

**Source:** `src/kernels/matrix_multiply.cu:150-220`

**Performance Impact:**
- Reduces thread count by COARSE_FACTOR²
- Increases register usage per thread
- Improves instruction-level parallelism
- Can reduce occupancy but increase throughput

---

## **18.4 Warp-Level Optimization**

Warp-level optimizations leverage the SIMT (Single Instruction, Multiple Thread) execution model to achieve maximum efficiency. Understanding warp behavior is crucial for avoiding performance pitfalls and utilizing specialized warp instructions.

### **Warp Execution Model**

The warp is the fundamental execution unit in CUDA, where 32 threads execute in lockstep:
- All threads in a warp execute the same instruction simultaneously
- Divergent branches serialize execution, reducing parallelism
- Warp shuffle instructions enable efficient thread communication without shared memory

### **Warp Shuffle Instructions**

Warp shuffle instructions allow direct register exchange between threads in a warp, eliminating the need for shared memory in many reduction and communication patterns:
```cpp
// Warp-level primitives (compute capability 3.0+)
__shfl_sync(mask, value, srcLane)     // Read from specific lane
__shfl_up_sync(mask, value, delta)    // Read from lane ID - delta
__shfl_down_sync(mask, value, delta)  // Read from lane ID + delta
__shfl_xor_sync(mask, value, laneMask) // XOR lane ID
```

### **Avoiding Warp Divergence**

Warp divergence occurs when threads within a warp take different execution paths, forcing serialization and reducing performance. Organizing conditionals to align with warp boundaries eliminates this overhead.

```cpp
// thread_operations.cu - Divergence examples
// BAD: Divergence within warp (threads 0-31 diverge)
if (threadIdx.x % 2 == 0) {
    // Even threads execute this path
    result[threadIdx.x] = data[threadIdx.x] * 2;
} else {
    // Odd threads execute this path - DIVERGENT!
    result[threadIdx.x] = data[threadIdx.x] + 1;
}
// Performance: 50% efficiency (serialized execution)

// GOOD: No divergence within warp (warps execute uniformly)
if ((threadIdx.x / 32) % 2 == 0) {
    // Even warps (warp 0, 2, 4...) execute uniformly
    result[threadIdx.x] = data[threadIdx.x] * 2;
} else {
    // Odd warps (warp 1, 3, 5...) execute uniformly
    result[threadIdx.x] = data[threadIdx.x] + 1;
}
// Performance: 100% efficiency (no divergence within warps)
```

**Source:** `src/part_specific/thread_operations.cu:45-75`

**Performance Comparison:**
- Divergent version: 2x slower due to serialization
- Non-divergent version: Full warp efficiency maintained

---

## **18.5 Occupancy Analysis**

Occupancy measures the ratio of active warps to the maximum possible warps on a streaming multiprocessor (SM). While higher occupancy often improves performance by hiding memory latency, it's not the only factor—instruction throughput and memory bandwidth also matter.

### **Occupancy Factors**

Four primary resources limit occupancy, and the most constraining resource determines the maximum achievable occupancy:

| Resource | Limit | Impact on Occupancy |
|----------|-------|---------------------|
| **Registers** | 65536 per SM | `Occupancy = min(1, MaxRegs / (RegsPerThread × ThreadsPerBlock))` |
| **Shared Memory** | 48-96 KB per SM | `Occupancy = min(1, MaxShared / SharedPerBlock)` |
| **Threads** | 2048 per SM | `Occupancy = min(1, MaxThreads / ThreadsPerBlock)` |
| **Blocks** | 32 per SM | `Occupancy = min(1, MaxBlocks / BlocksNeeded)` |

### **Occupancy Calculator API**

CUDA provides runtime APIs to determine optimal launch configurations based on kernel resource usage. These functions analyze register and shared memory requirements to suggest configurations that maximize occupancy.

```cpp
// thread_hierarchy_demo.cu - Occupancy calculation example
int min_grid_size, optimal_block_size;
cudaOccupancyMaxPotentialBlockSize(
    &min_grid_size,           // Minimum grid size for max occupancy
    &optimal_block_size,      // Optimal block size
    matmul_tiled_basic<16>,   // Kernel function
    0,                        // Dynamic shared memory (0 if static only)
    0);                       // Max block size (0 = no limit)

printf("Optimal block size: %d\n", optimal_block_size);
printf("Minimum grid size for max occupancy: %d\n", min_grid_size);

// Calculate occupancy for specific configuration
int max_active_blocks;
cudaOccupancyMaxActiveBlocksPerMultiprocessor(
    &max_active_blocks,
    matmul_tiled_basic<16>,
    256,  // threads per block
    0);   // dynamic shared memory

float occupancy = (max_active_blocks * 256) / (float)max_warps_per_sm;
printf("Estimated occupancy: %.2f%%\n", occupancy * 100);
```

**Source:** `src/part_specific/thread_hierarchy_demo.cu:120-150`

**Practical Example:**
```
Optimal block size: 256
Minimum grid size for max occupancy: 512
Estimated occupancy: 75.00%

Kernel launched with: <<<512, 256>>>
Achieved occupancy: 75.2% (measured)
```

---

## **18.6 Testing Thread Hierarchy Functions**

Part 18 includes comprehensive tests for thread hierarchy optimizations. Tests use the `GpuTest` base class from [00.test_lib/gpu_gtest.h](../../00.test_lib/gpu_gtest.h) for automatic device setup/teardown.

### **18.6.1 Tested Kernels**

The following thread hierarchy implementations are tested:

**Matrix Multiplication Variants** ([test/unit/kernels/test_matrix_multiply.cu](test/unit/kernels/test_matrix_multiply.cu)):
- `matmul_tiled_basic<16>()` - Square tile implementation (16x16)
- `matmul_tiled_basic<32>()` - Square tile implementation (32x32)
- `matmul_coarsened<2>()` - Thread coarsening with factor 2
- `matmul_coarsened<4>()` - Thread coarsening with factor 4

**Thread Operations** ([test/unit/part_specific/test_thread_operations.cu](test/unit/part_specific/test_thread_operations.cu)):
- Warp divergence comparisons (divergent vs. non-divergent)
- Thread indexing correctness
- Block/grid configuration validation

### **18.6.2 Test Examples**

```cpp
// test_matrix_multiply.cu - Testing tiled matrix multiplication
GPU_TEST_F(MatrixMultiplyTest, Tiled16x16) {
    const int N = 512;
    const int TILE_SIZE = 16;

    dim3 block(TILE_SIZE, TILE_SIZE);
    dim3 grid((N + TILE_SIZE - 1) / TILE_SIZE,
              (N + TILE_SIZE - 1) / TILE_SIZE);

    matmul_tiled_basic<TILE_SIZE><<<grid, block>>>(d_A, d_B, d_C, N);
    CHECK_KERNEL_LAUNCH();

    // Verify against CPU reference
    cudaMemcpy(h_C, d_C, bytes, cudaMemcpyDeviceToHost);
    for (int i = 0; i < N * N; i++) {
        EXPECT_NEAR(h_C[i], h_C_ref[i], 1e-2f);
    }
}

// test_thread_operations.cu - Testing warp divergence impact
GPU_TEST(ThreadOps, WarpDivergence) {
    const int N = 1024;
    float *d_result_divergent, *d_result_aligned;

    // Test divergent pattern
    divergent_kernel<<<32, 32>>>(d_result_divergent, N);
    float time_divergent = measure_time();

    // Test warp-aligned pattern
    aligned_kernel<<<32, 32>>>(d_result_aligned, N);
    float time_aligned = measure_time();

    // Aligned version should be ~2x faster
    EXPECT_LT(time_aligned, time_divergent * 0.6f);
}
```

### **18.6.3 Running Thread Hierarchy Tests**

```bash
# Run all Part 18 tests
./10.cuda_basic/18.Thread_Hierarchy_Practice/18_Thread_Hierarchy_Practice_test

# Run only matrix multiplication tests
./10.cuda_basic/18.Thread_Hierarchy_Practice/18_Thread_Hierarchy_Practice_test --gtest_filter="*MatMul*"

# Run only thread operation tests
./10.cuda_basic/18.Thread_Hierarchy_Practice/18_Thread_Hierarchy_Practice_test --gtest_filter="*ThreadOps*"
```

---

## **18.7 Running the Examples**

### **Building**
```bash
cd build
cmake --build . --target 18_Thread_Hierarchy_Practice
```

### **Running Main Demo**
```bash
# Run with default matrix size
./10.cuda_basic/18.Thread_Hierarchy_Practice/18_Thread_Hierarchy_Practice

# Run with custom size
./10.cuda_basic/18.Thread_Hierarchy_Practice/18_Thread_Hierarchy_Practice 1024
```

### **Running Tests**
```bash
# Run all tests using CTest
ctest -R 18_Thread_Hierarchy_Practice

# Run with verbose output
./10.cuda_basic/18.Thread_Hierarchy_Practice/18_Thread_Hierarchy_Practice_test --gtest_color=yes
```

**Expected Test Output:**
```
[==========] Running 8 tests from 2 test suites.
[----------] 5 tests from MatrixMultiplyTest
[ RUN      ] MatrixMultiplyTest.Tiled16x16
[       OK ] MatrixMultiplyTest.Tiled16x16 (45 ms)
[ RUN      ] MatrixMultiplyTest.Tiled32x32
[       OK ] MatrixMultiplyTest.Tiled32x32 (52 ms)
[ RUN      ] MatrixMultiplyTest.CoarseningFactor2
[       OK ] MatrixMultiplyTest.CoarseningFactor2 (38 ms)
[----------] 5 tests from MatrixMultiplyTest (220 ms total)

[----------] 3 tests from ThreadOps
[ RUN      ] ThreadOps.WarpDivergence
[       OK ] ThreadOps.WarpDivergence (18 ms)
[----------] 3 tests from ThreadOps (55 ms total)

[==========] 8 tests from 2 test suites ran. (275 ms total)
[  PASSED  ] 8 tests.
```

---

## **18.8 Profiling and Analysis**

This section provides comprehensive profiling commands for analyzing thread hierarchy performance. These tools help identify occupancy bottlenecks, warp divergence, and opportunities for optimization.

### **18.8.1 Nsight Systems - System-Wide Thread Analysis**

Nsight Systems provides high-level overview of thread hierarchy and kernel launches.

**Basic Thread Profiling:**
```bash
# Profile with CUDA thread information
nsys profile --trace=cuda,nvtx --cuda-thread-trace=true \
    --stats=true -o thread_profile ./18_Thread_Hierarchy_Practice

# View kernel launch configuration
nsys stats --report cuda_gpu_kern_sum thread_profile.nsys-rep

# Example output:
# Kernel Name             Grid Size    Block Size   Regs/Thr  Shared Mem
# matmul_tiled_basic<16>  (64,64,1)    (16,16,1)    32        4096 bytes
# matmul_coarsened        (32,32,1)    (16,16,1)    48        8192 bytes
```

**Thread Execution Timeline:**
```bash
# Generate timeline with thread details
nsys profile --trace=cuda --show-output=true \
    --cuda-graph-trace=node -o timeline ./18_Thread_Hierarchy_Practice

# Open in GUI for visual analysis
nsys-ui timeline.nsys-rep
# Look for: kernel duration, grid/block config, overlapping execution
```

**Identifying Launch Inefficiencies:**
```bash
# Check for small kernel launches (underutilization)
nsys stats --report cuda_gpu_kern_sum thread_profile.nsys-rep \
    | awk '$8 < 1000' # Kernels with < 1000 threads total

# Expected: Most kernels should use 10K+ threads for good GPU utilization
```

### **18.8.2 Nsight Compute - Detailed Thread Metrics**

Nsight Compute provides kernel-level thread hierarchy analysis with actionable insights.

**Occupancy Profiling:**
```bash
# Comprehensive occupancy analysis
ncu --metrics sm__warps_active.avg.pct_of_peak_sustained_active,\
sm__maximum_warps_per_active_cycle_pct,\
launch__occupancy_limit_blocks,\
launch__occupancy_limit_registers,\
launch__occupancy_limit_shared_mem \
    --kernel-name "matmul_tiled_basic" \
    ./18_Thread_Hierarchy_Practice

# Example output interpretation:
# sm__warps_active.avg.pct: 65%  -> Good occupancy
# launch__occupancy_limit: blocks -> Limited by block count, increase blocks
# launch__occupancy_limit: registers -> Too many regs, reduce or increase block size
```

**Detailed Occupancy Report:**
```bash
# Generate full occupancy report
ncu --set full --section Occupancy -o occupancy_report \
    ./18_Thread_Hierarchy_Practice

# Key metrics to examine:
# - Theoretical Occupancy: Based on resource usage
# - Achieved Occupancy: Actual runtime occupancy
# - Limiting Factor: What resource limits occupancy
#   (blocks, warps, registers, shared memory)
```

**Occupancy Comparison Table:**

| Kernel | Blocks/SM | Warps/SM | Occupancy | Limiting Factor | Recommendation |
|--------|-----------|----------|-----------|-----------------|----------------|
| Tile 8x8 | 8 | 16 | 50% | Blocks | Increase block size |
| Tile 16x16 | 4 | 16 | 75% | Registers | Good balance |
| Tile 32x32 | 2 | 16 | 50% | Shared Mem | Use smaller tiles |
| Coarsened | 6 | 24 | 87% | None | Excellent |

### **Thread Hierarchy Analysis**

Analyze thread organization and resource usage:
```bash
# Using inspect_profile.cmake profiling targets
make 18_Thread_Hierarchy_Practice_nsys_profile

# View thread hierarchy metrics
nsys stats --report cuda_gpu_kern_sum report.nsys-rep

# Check thread block configuration
nsys stats --report cuda_api_sum report.nsys-rep | grep "cudaLaunch"
```

**Key Metrics:**
- Threads per block: Should be multiple of 32 (warp size)
- Blocks per grid: Should saturate GPU (>= # of SMs × 4)
- Active warps per SM: Higher is better for latency hiding
- Theoretical vs. achieved occupancy: Should be within 10-20%

### **18.8.3 Warp Divergence Analysis**

Identify and quantify warp divergence impact with detailed profiling.

**Divergence Detection:**
```bash
# Profile branch divergence metrics
ncu --metrics smsp__branch_targets_threads_divergent.pct,\
smsp__sass_branch_targets_threads_divergent.sum,\
smsp__sass_branch_targets.sum \
    --kernel-name "divergent_kernel" \
    ./18_Thread_Hierarchy_Practice

# Example output:
# smsp__branch_targets_threads_divergent.pct: 35.2%  -> High divergence!
# smsp__sass_branch_targets_threads_divergent: 15360 -> Divergent branches
# smsp__sass_branch_targets: 43520 -> Total branches
# Divergence ratio: 15360/43520 = 35.3% (needs optimization)
```

**Warp Execution Efficiency:**
```bash
# Measure thread execution efficiency
ncu --metrics smsp__thread_inst_executed_per_inst_executed.ratio \
    ./18_Thread_Hierarchy_Practice

# Interpretation:
# Ratio = 1.0: Perfect (no divergence)
# Ratio = 0.5: 50% efficiency (half threads active)
# Ratio < 0.3: Severe divergence, refactor needed
```

**Divergence Visualization:**
```bash
# Generate detailed divergence report
ncu --set full --section SourceCounters \
    --kernel-name "divergent_kernel" \
    -o divergence_report ./18_Thread_Hierarchy_Practice

# View in GUI to see source-level divergence
ncu-ui divergence_report.ncu-rep
# Highlights: lines causing divergence, severity, fix suggestions
```

**Divergence Benchmarks:**

| Kernel Pattern | Divergence % | Warp Efficiency | Performance Impact |
|----------------|--------------|-----------------|-------------------|
| Uniform condition | 0% | 100% | Baseline (1.0x) |
| Even/odd threads | 50% | 50% | 0.5x slower |
| Modulo condition | 75% | 25% | 0.25x slower |
| Random condition | 85% | 15% | 0.15x slower |

**Expected Metrics:**
- Divergent branch percentage < 5% (good)
- Divergent branch percentage 5-20% (acceptable)
- Divergent branch percentage > 20% (needs optimization)
- Thread inst ratio > 0.8 (good)
- Thread inst ratio < 0.5 (poor, investigate)

### **Occupancy Analysis**

Measure and optimize GPU occupancy:
```bash
# Detailed occupancy analysis with Nsight Compute
ncu --metrics sm__warps_active.avg.pct_of_peak_sustained_active \
    ./10.cuda_basic/18.Thread_Hierarchy_Practice/18_Thread_Hierarchy_Practice

# Occupancy calculator (compile-time estimation)
make 18_Thread_Hierarchy_Practice_nsight_compute
```

**Target Occupancy:**
- 50-75%: Good for most kernels
- 75-100%: Excellent for memory-bound kernels
- <50%: May indicate resource overuse

### **Tile Size Comparison**

Compare performance across different tile configurations:
```bash
# Run benchmark with multiple tile sizes
./10.cuda_basic/18.Thread_Hierarchy_Practice/18_Thread_Hierarchy_Practice 512

# Profile specific tile size
ncu --kernel-name "matmul_tiled_basic<16>" \
    ./10.cuda_basic/18.Thread_Hierarchy_Practice/18_Thread_Hierarchy_Practice
```

**Performance Comparison (N=1024):**
```
Tile 8x8:   150 GFLOPS, 75% occupancy, 2KB shared mem
Tile 16x16: 280 GFLOPS, 88% occupancy, 4KB shared mem
Tile 32x32: 320 GFLOPS, 75% occupancy, 8KB shared mem
```

### **Thread Coarsening Analysis**

Measure the impact of thread coarsening:
```bash
# Compare coarsening factors
ncu --set full --section LaunchStats \
    --kernel-name "matmul_coarsened" \
    ./10.cuda_basic/18.Thread_Hierarchy_Practice/18_Thread_Hierarchy_Practice
```

**Expected Results:**
- Coarsening Factor 2: 25% fewer threads, 15% speedup
- Coarsening Factor 4: 75% fewer threads, 30% speedup
- Diminishing returns beyond factor 4 due to register pressure

---

## **18.9 Expected Output**

```
Using device: NVIDIA TITAN RTX
Compute capability: 7.5

=== Thread Hierarchy Analysis ===
Device Limits:
  Max threads per block: 1024
  Max thread dimensions: (1024, 1024, 64)
  Max grid dimensions: (2147483647, 65535, 65535)
  Warp size: 32
  Max warps per SM: 64
  Max blocks per SM: 32

=== Occupancy Analysis ===
Block size   64: Occupancy = 50.0% (Max active blocks: 32)
Block size  128: Occupancy = 100.0% (Max active blocks: 16)
Block size  256: Occupancy = 100.0% (Max active blocks: 8)
Block size  512: Occupancy = 100.0% (Max active blocks: 4)
Block size 1024: Occupancy = 100.0% (Max active blocks: 2)
Optimal block size suggested: 256

=== Warp Divergence Impact ===
With warp divergence: 1.234 ms
Without warp divergence: 0.456 ms
Speedup from avoiding divergence: 2.7x

=== Thread Hierarchy Benchmark ===
Matrix size: 512 x 512

Kernel Performance:
-----------------------------------------------------------------
                          Tiled 8x8:   12.345 ms,  43.21 GFLOPS
                        Tiled 16x16:    8.234 ms,  64.78 GFLOPS
                        Tiled 32x32:    9.123 ms,  58.45 GFLOPS
             Rectangular tiles 8x32:    7.892 ms,  67.54 GFLOPS
                      Warp optimized:    6.789 ms,  78.52 GFLOPS

Verifying correctness...
Results verified: PASS

=== Thread Hierarchy Demo Complete ===
```

---

## **18.10 Performance Guidelines**

### **Block Size Selection**

| Block Size | Pros | Cons | Best For |
|------------|------|------|----------|
| **64-128** | High occupancy potential | Low parallelism | Memory-bound kernels |
| **256** | Balanced | Standard choice | General purpose |
| **512-1024** | Maximum parallelism | May limit occupancy | Compute-bound kernels |

### **Tile Size Impact**

| Tile Size | Shared Memory | Occupancy | Performance |
|-----------|---------------|-----------|-------------|
| **8x8** | 256 bytes | High | Good for small matrices |
| **16x16** | 1 KB | Balanced | General purpose |
| **32x32** | 4 KB | May be limited | Large matrices |

---

## **18.11 Common Issues and Solutions**

### **Problem 1: Low Occupancy**
**Symptoms**: Poor GPU utilization
**Solutions**:
- Reduce register usage
- Decrease shared memory per block
- Adjust block size

### **Problem 2: Warp Divergence**
**Symptoms**: Poor performance in conditional code
**Solutions**:
- Reorganize conditions to align with warp boundaries
- Use warp-level primitives
- Restructure algorithm

### **Problem 3: Unbalanced Workload**
**Symptoms**: Some blocks finish much earlier
**Solutions**:
- Use dynamic scheduling
- Implement work stealing
- Better work distribution

### **Problem 4: Register Spilling**
**Symptoms**: Local memory usage in profiler
**Solutions**:
- Reduce variables per thread
- Use shared memory for temporary storage
- Enable `-maxrregcount` compiler flag

---

## **18.12 Optimization Techniques**

### **1. Persistent Threads**
```cpp
__global__ void persistent_kernel(int* work_queue) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;
    int work_item;

    while ((work_item = atomicAdd(work_queue, 1)) < total_work) {
        // Process work_item
    }
}
```

### **2. Grid-Stride Loops**
```cpp
__global__ void grid_stride_kernel(int n) {
    for (int i = blockIdx.x * blockDim.x + threadIdx.x;
         i < n;
         i += blockDim.x * gridDim.x) {
        // Process element i
    }
}
```

---

## **18.13 Exercises**

### **Exercise 1: Optimal Tile Size**
Find the optimal tile size for your GPU:
```cpp
// Test tile sizes: 4, 8, 12, 16, 20, 24, 28, 32
// Measure performance and occupancy
```

### **Exercise 2: Warp Specialization**
Implement a kernel where different warps perform different tasks:
```cpp
int warp_id = threadIdx.x / 32;
if (warp_id == 0) {
    // Data loading
} else if (warp_id == 1) {
    // Computation
} else {
    // Data storing
}
```

### **Exercise 3: Occupancy Tuning**
Use `__launch_bounds__` to control occupancy:
```cpp
__global__ void
__launch_bounds__(256, 8)  // max threads, min blocks
optimized_kernel() { }
```

### **Exercise 4: Thread Coarsening Study**
Implement varying coarsening factors and measure:
- Performance impact
- Register usage
- Occupancy changes

---

## **18.14 Best Practices**

1. **Start with 256 threads per block** - Good default for most kernels
2. **Align block dimensions with warp size** - Use multiples of 32
3. **Minimize warp divergence** - Keep conditional paths aligned
4. **Balance resources** - Don't max out one resource
5. **Profile before optimizing** - Identify actual bottlenecks
6. **Consider problem size** - Small problems may need different strategies
7. **Test multiple configurations** - Optimal settings vary by GPU

---

## **18.15 Advanced Topics**

This section introduces advanced parallelism concepts that extend beyond basic thread hierarchy. Full implementations are covered in later modules.

### **18.15.1 Cooperative Groups**

Cooperative Groups provide modern, flexible thread synchronization beyond traditional `__syncthreads()`. This API enables fine-grained control over thread grouping and synchronization.

**Basic Usage:**
```cpp
#include <cooperative_groups.h>
namespace cg = cooperative_groups;

__global__ void coop_kernel(int* data, int n) {
    // Traditional block-level group
    cg::thread_block block = cg::this_thread_block();

    // Partition block into warps (32 threads each)
    cg::thread_block_tile<32> warp = cg::tiled_partition<32>(block);

    // Partition into smaller tiles (e.g., 16 threads)
    cg::thread_block_tile<16> tile = cg::tiled_partition<16>(block);

    int tid = block.thread_rank();
    int value = data[tid];

    // Warp-level reduction (no shared memory needed!)
    int warp_sum = cg::reduce(warp, value, cg::plus<int>());

    // Tile-level reduction
    int tile_sum = cg::reduce(tile, value, cg::plus<int>());

    // Flexible synchronization
    tile.sync();  // Sync only within tile, not entire block
}
```

**Advanced: Grid-Wide Synchronization:**
```cpp
__global__ void grid_sync_kernel(int* data) {
    cg::grid_group grid = cg::this_grid();

    // Phase 1: All threads work
    process_data(data);

    // Synchronize ALL threads across ALL blocks
    grid.sync();  // Requires cooperative launch

    // Phase 2: Continue after global sync
    finalize_data(data);
}

// Launch with cooperative API
void launch_cooperative() {
    cudaLaunchCooperativeKernel((void*)grid_sync_kernel, grid, block, args);
}
```

**Performance Benefits:**
- Warp-level ops 5-10x faster than shared memory reduction
- Flexible granularity (2, 4, 8, 16, 32 threads)
- Cleaner code, less error-prone

**➡️ Detailed Coverage:** [Part 21: Synchronization and Atomics](../../../20.cuda_intermediate/21.Synchronization_and_Atomics/README.md)

### **18.15.2 Tensor Cores (Volta+)**

Tensor Cores are specialized hardware units for matrix operations, providing 8-10x speedup over traditional CUDA cores for mixed-precision workloads.

**WMMA (Warp Matrix Multiply-Accumulate):**
```cpp
#include <mma.h>
using namespace nvcuda;

__global__ void tensor_core_gemm(half* A, half* B, float* C, int M, int N, int K) {
    // Declare fragments (register storage for matrix tiles)
    wmma::fragment<wmma::matrix_a, 16, 16, 16, half, wmma::row_major> a_frag;
    wmma::fragment<wmma::matrix_b, 16, 16, 16, half, wmma::col_major> b_frag;
    wmma::fragment<wmma::accumulator, 16, 16, 16, float> c_frag;

    int warpM = (blockIdx.x * blockDim.x + threadIdx.x) / 32;
    int warpN = (blockIdx.y * blockDim.y + threadIdx.y);

    // Initialize accumulator to zero
    wmma::fill_fragment(c_frag, 0.0f);

    // Perform matrix multiplication on 16x16 tiles
    for (int i = 0; i < K; i += 16) {
        int aRow = warpM * 16;
        int aCol = i;
        int bRow = i;
        int bCol = warpN * 16;

        // Load 16x16 tiles from A and B
        wmma::load_matrix_sync(a_frag, A + aRow * K + aCol, K);
        wmma::load_matrix_sync(b_frag, B + bRow * N + bCol, N);

        // Perform 16x16x16 matrix multiply-accumulate
        wmma::mma_sync(c_frag, a_frag, b_frag, c_frag);
    }

    // Store result back to global memory
    wmma::store_matrix_sync(C + warpM * 16 * N + warpN * 16, c_frag, N, wmma::mem_row_major);
}
```

**Performance Characteristics:**
- FP16 inputs → FP32 accumulation
- 16x16 matrix tiles processed per warp
- Throughput: ~125 TFLOPS (A100), ~312 TFLOPS (H100)
- 8-12x faster than equivalent FP32 CUDA cores

**When to Use:**
- Deep learning (training, inference)
- Scientific computing with acceptable precision
- Matrix dimensions multiple of 16
- GPU with Tensor Cores (Volta, Turing, Ampere, Hopper)

**➡️ Detailed Coverage:** Part 48: Tile-Based Programming (Advanced Module)

### **18.15.3 Dynamic Parallelism**

Dynamic Parallelism allows GPU threads to launch child kernels from device code, enabling recursive and adaptive algorithms entirely on GPU.

**Basic Child Kernel Launch:**
```cpp
__global__ void child_kernel(int* data, int offset, int size) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;
    if (tid < size) {
        data[offset + tid] = tid * tid;
    }
}

__global__ void parent_kernel(int* data, int n) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;

    // Each parent thread launches a child kernel
    if (tid < n) {
        int chunk_size = 256;
        int offset = tid * chunk_size;

        dim3 child_grid((chunk_size + 255) / 256);
        dim3 child_block(256);

        // Launch child kernel from device
        child_kernel<<<child_grid, child_block>>>(data, offset, chunk_size);

        // Wait for child to complete (optional)
        cudaDeviceSynchronize();
    }
}
```

**Recursive Quicksort Example:**
```cpp
__global__ void quicksort(int* data, int left, int right) {
    if (left >= right) return;

    // Partition data around pivot
    int pivot = partition(data, left, right);

    // Launch child kernels for sub-arrays
    if (pivot - left > 1) {
        quicksort<<<1, 1>>>(data, left, pivot - 1);
    }
    if (right - pivot > 1) {
        quicksort<<<1, 1>>>(data, pivot + 1, right);
    }

    // Parent waits for children
    cudaDeviceSynchronize();
}
```

**Adaptive Mesh Refinement:**
```cpp
__global__ void refine_mesh(Cell* cells, int* refine_flags, int n) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;

    if (tid < n && refine_flags[tid]) {
        // This cell needs refinement
        Cell* children = allocate_children(cells[tid]);

        // Launch kernel to process refined cells
        dim3 grid(8);  // 8 child cells
        dim3 block(64);
        process_refined<<<grid, block>>>(children, cells[tid].properties);
    }
}
```

**Performance Considerations:**
- Overhead: ~5-10 μs per kernel launch from device
- Best for irregular workloads where CPU launch overhead is prohibitive
- Requires compute capability 3.5+ (Kepler+)
- Consumes device-side heap memory for launch metadata

**Use Cases:**
- Recursive algorithms (quicksort, tree traversal)
- Adaptive simulations (mesh refinement, particle systems)
- Irregular parallelism (variable workload per thread)
- Eliminating CPU-GPU synchronization in multi-stage algorithms

**➡️ Detailed Coverage:** [Part 25: Dynamic Parallelism](../../../20.cuda_intermediate/25.Dynamic_Parallelism/README.md)

### **18.15.4 Thread Block Clusters (Hopper+)**

Thread Block Clusters group multiple thread blocks for distributed shared memory access, available on H100 and newer GPUs.

**Basic Cluster Usage:**
```cpp
#include <cuda/cluster>

__global__ void __cluster_dims__(2, 2, 1)  // 2x2 cluster of blocks
cluster_kernel(float* data) {
    // Access cluster dimensions
    dim3 cluster_dim = cluster::cluster_dim();      // (2, 2, 1)
    dim3 cluster_idx = cluster::cluster_idx();      // This cluster's index
    dim3 block_idx_in_cluster = cluster::block_rank(); // Block index within cluster

    // Distributed shared memory (accessible across cluster)
    __shared__ float tile[256];

    // Cluster-wide synchronization
    cluster::sync();

    // Access shared memory from neighboring blocks
    float* neighbor_tile = cluster::map_shared_rank(tile, neighbor_rank);
}
```

**Performance Gains:**
- 2-3x improvement for stencil computations
- Enables larger tiles without register pressure
- Better data locality for block-to-block communication

**➡️ Detailed Coverage:** Part 49: Thread Block Clusters (Advanced Module)

---

## **18.16 Profiler Metrics**

### **Key Metrics to Monitor**
- `sm__threads_launched.sum`: Total threads launched
- `sm__warps_launched.sum`: Total warps launched
- `sm__maximum_warps_per_active_cycle_pct`: Warp occupancy
- `smsp__thread_inst_executed_per_inst_executed.ratio`: Thread efficiency
- `smsp__branch_targets_threads_divergent.pct`: Divergence percentage

---

## **18.17 Thread Hierarchy Glossary**

Quick reference for CUDA thread hierarchy terminology and concepts.

### **Core Concepts**

**Thread**: The smallest unit of execution in CUDA. Each thread has its own thread ID (`threadIdx`) and executes the same kernel code with different data. Threads have private register and local memory.

**Warp**: A group of 32 consecutive threads that execute in SIMT (Single Instruction, Multiple Thread) fashion. All threads in a warp execute the same instruction simultaneously, though they may operate on different data.

**Block (Thread Block)**: A group of threads (up to 1024) that can cooperate via shared memory and synchronize using `__syncthreads()`. Blocks are assigned a block ID (`blockIdx`) within the grid.

**Grid**: The collection of all thread blocks launched by a single kernel. Grid dimensions define how many blocks exist in each dimension (x, y, z).

**SM (Streaming Multiprocessor)**: Physical hardware unit that executes thread blocks. Modern GPUs have dozens of SMs, each capable of running multiple blocks concurrently.

### **Thread Indexing**

**threadIdx**: Built-in variable containing the thread's index within its block (threadIdx.x, threadIdx.y, threadIdx.z). Range: 0 to blockDim-1.

**blockIdx**: Built-in variable containing the block's index within the grid (blockIdx.x, blockIdx.y, blockIdx.z). Range: 0 to gridDim-1.

**blockDim**: Built-in variable containing the number of threads per block in each dimension (blockDim.x, blockDim.y, blockDim.z).

**gridDim**: Built-in variable containing the number of blocks in the grid in each dimension (gridDim.x, gridDim.y, gridDim.z).

**Global Thread ID Calculation**:
- 1D: `int tid = blockIdx.x * blockDim.x + threadIdx.x;`
- 2D: `int tid = (blockIdx.y * gridDim.x + blockIdx.x) * (blockDim.x * blockDim.y) + (threadIdx.y * blockDim.x + threadIdx.x);`

### **Execution Model**

**SIMT (Single Instruction, Multiple Thread)**: Execution model where all threads in a warp execute the same instruction simultaneously. Different from SIMD as threads can diverge via if/else statements.

**Warp Divergence**: When threads in a warp take different execution paths (e.g., some take if-branch, others take else-branch). Causes serialization and performance loss. Both paths execute, with threads masked off for the path they don't take.

**Occupancy**: Ratio of active warps to maximum possible warps on an SM. Higher occupancy can hide memory latency but doesn't always mean better performance. Formula: `occupancy = active_warps / max_warps_per_sm`.

**Latency Hiding**: Technique where the GPU switches to other warps while one warp waits for memory. Requires sufficient occupancy to have enough warps ready to execute.

### **Memory and Synchronization**

**Shared Memory**: Fast on-chip memory (48-96 KB per block) shared among all threads in a block. Explicitly managed by programmer. Much faster than global memory (~20-30 cycles vs ~440 cycles).

**__syncthreads()**: Block-level barrier synchronization. All threads in the block must reach this point before any can proceed. Used to ensure shared memory operations complete before dependent operations.

**Warp Synchronous Programming**: Writing code that relies on implicit synchronization within a warp. Deprecated in favor of explicit cooperative groups or shuffle instructions.

**Warp Shuffle**: Instructions (`__shfl_*`) that allow threads within a warp to exchange data without using shared memory. Very fast (1-2 cycles) but limited to warp scope.

### **Tiling and Optimization**

**Tiling**: Breaking a large problem into smaller chunks (tiles) that fit in shared memory. Reduces global memory accesses by reusing data in fast shared memory. Essential for matrix operations.

**Tile Size**: Dimensions of each tile. Common sizes: 16x16, 32x32 for matrices. Choice affects occupancy (shared memory usage) and performance (data reuse).

**Thread Coarsening**: Having each thread process multiple data elements instead of one. Reduces synchronization overhead and can improve instruction-level parallelism. Example: each thread processes 4 elements instead of 1.

**Register Pressure**: When a kernel uses too many registers per thread, limiting occupancy. Can cause register spilling to slow local memory. Solution: reduce variables, use smaller data types, or adjust block size.

### **Performance Metrics**

**Active Threads**: Number of threads currently executing or ready to execute on an SM. Higher is generally better for latency hiding.

**Warp Execution Efficiency**: Percentage of threads in a warp that are active during execution. 100% means no divergence, <50% indicates significant divergence.

**Thread Block Limit**: Hardware constraint on maximum blocks per SM (typically 16-32). Can limit occupancy even when other resources are available.

**Achieved Occupancy**: Actual occupancy measured during kernel execution. May be lower than theoretical due to runtime factors (memory latency, divergence).

### **Common Patterns**

**Grid-Stride Loop**: Pattern where threads process multiple elements by striding through data:
```cpp
for (int i = blockIdx.x * blockDim.x + threadIdx.x;
     i < N;
     i += blockDim.x * gridDim.x) {
    process(data[i]);
}
```

**Reduction**: Combining values from all threads into a single result. Requires careful synchronization and typically uses shared memory + warp shuffles for efficiency.

**Collaborative Loading**: Pattern where all threads in a block work together to load data into shared memory, maximizing memory bandwidth:
```cpp
__shared__ float tile[TILE_SIZE][TILE_SIZE];
tile[threadIdx.y][threadIdx.x] = global_data[...];
__syncthreads();
```

### **Advanced Concepts**

**Cooperative Groups**: Modern API for flexible thread grouping and synchronization beyond traditional blocks. Allows subset synchronization, grid-wide sync, and more.

**Warp-Level Primitives**: Low-level operations like `__ballot()`, `__any()`, `__all()` that operate on warp masks. Used for efficient warp-level algorithms.

**Dynamic Parallelism**: Feature allowing GPU threads to launch new kernels from device code. Useful for recursive algorithms and adaptive workloads.

**Tensor Cores**: Specialized hardware for matrix multiply-accumulate operations. Operate on 4x4 or 8x8 matrix tiles, providing massive speedup for deep learning and scientific computing.

### **Launch Configuration**

**Kernel Launch Syntax**: `kernel<<<gridDim, blockDim, sharedMemBytes, stream>>>(args);`
- `gridDim`: Number of blocks (dim3)
- `blockDim`: Threads per block (dim3)
- `sharedMemBytes`: Dynamic shared memory (optional, bytes)
- `stream`: CUDA stream for async execution (optional)

**Optimal Configuration**: Depends on kernel characteristics:
- Compute-bound: Maximize occupancy, use 256-512 threads/block
- Memory-bound: Focus on memory access patterns, may use fewer threads
- Always profile: Optimal configuration varies by GPU architecture and workload

---

## **18.18 References**

- [CUDA Programming Guide - Thread Hierarchy](https://docs.nvidia.com/cuda/cuda-c-programming-guide/index.html#thread-hierarchy)
- [Occupancy Calculator](https://docs.nvidia.com/cuda/cuda-occupancy-calculator/index.html)
- [Warp-Level Primitives](https://developer.nvidia.com/blog/using-cuda-warp-level-primitives/)
- [Cooperative Groups](https://developer.nvidia.com/blog/cooperative-groups/)

---

## **18.19 Summary**

This section demonstrated:
- Thread hierarchy organization and limits
- Various tiling strategies and their trade-offs
- Warp-level optimization techniques
- Occupancy analysis and tuning
- Avoiding warp divergence
- Thread coarsening benefits

**Key Takeaways:**
- Thread organization significantly impacts performance
- Optimal configuration depends on kernel characteristics
- Warp divergence can severely impact performance
- Occupancy is important but not the only factor
- Profile-guided optimization is essential

---

📄 **Next**: [Part 19: CUDA Memory API](../19.CUDA_Memory_API/README.md)