# 💾 Part 19: CUDA Memory API

**Goal**: Master CUDA memory management APIs including allocation strategies, transfer optimizations, and advanced memory features.

---

## **19.1 Overview**

The CUDA Memory API provides comprehensive control over GPU memory management. This section covers:
- Memory allocation strategies
- Transfer optimization techniques
- Unified memory management
- Pinned and mapped memory
- Memory pools and async operations
- Texture and constant memory
- Performance measurement and profiling

---

## **19.2 Memory Types and APIs**

### **Visual Memory Flow**

```
CPU/HOST SIDE                     GPU/DEVICE SIDE
=============                     ===============

┌─────────────────┐              ┌──────────────────┐
│  Pageable RAM   │              │  Global Memory   │
│  (malloc)       │              │  (cudaMalloc)    │
│                 │              │                  │
│  Slow transfer  │───────X──────│  Device DRAM     │
│  ~6 GB/s PCIe   │              │  ~900 GB/s BW    │
└─────────────────┘              └──────────────────┘
                                          │
┌─────────────────┐                       │
│  Pinned Memory  │                       │
│ (cudaHostAlloc) │                       ▼
│                 │              ┌──────────────────┐
│  Fast transfer  │──────────────│  L2 Cache        │
│  ~12 GB/s PCIe  │  cudaMemcpy  │  (4-6 MB)        │
│                 │◄─────────────│  ~2 TB/s         │
│  DMA capable    │              └──────────────────┘
└─────────────────┘                       │
         │                                │
         │                                ▼
         │                       ┌──────────────────┐
         │                       │  L1/Tex Cache    │
         │                       │  (128 KB/SM)     │
         │                       │  ~4 TB/s         │
         │                       └──────────────────┘
         │                                │
         ▼                                ▼
┌─────────────────┐              ┌──────────────────┐
│  Unified Memory │              │  Shared Memory   │
│(cudaMallocMgd)  │              │  (__shared__)    │
│                 │              │                  │
│  Auto-migrated  │◄────────────►│  On-chip SRAM    │
│  On-demand      │   Managed    │  ~1.5 TB/s       │
│  Page faults    │   by Driver  │  48-96 KB/block  │
└─────────────────┘              └──────────────────┘

Memory Transfer Patterns:
========================

Pattern 1: Explicit Transfer (Best Performance)
Host Pinned ─┬─→ cudaMemcpyAsync ─→ Device Global
             │                       (12 GB/s PCIe)
             └─→ Overlap with Kernel ─→ Process

Pattern 2: Zero-Copy (Low Latency)
Host Mapped ───→ Direct Access ───→ Device reads via PCIe
(cudaHostAllocMapped)              (6-8 GB/s, no copy)

Pattern 3: Unified Memory (Easiest)
Managed Memory ─→ Auto Page Migration ─→ Wherever Accessed
               Driver handles transfers (8-10 GB/s)
               Page faults on first access
```

### **Memory Type Comparison**

| Memory Type | Allocation API | Location | Access | Cache | Lifetime | Bandwidth |
|------------|---------------|----------|--------|-------|----------|-----------|
| **Global** | `cudaMalloc()` | Device | R/W | L1/L2 | Explicit | ~900 GB/s |
| **Shared** | `__shared__` | On-chip | R/W | N/A | Block | ~1.5 TB/s |
| **Local** | Automatic | Off-chip | R/W | L1/L2 | Thread | ~900 GB/s |
| **Constant** | `cudaMemcpyToSymbol()` | Device | R | Yes | Application | ~800 GB/s |
| **Texture** | Texture API | Device | R | Yes | Explicit | ~800 GB/s |
| **Pinned** | `cudaHostAlloc()` | Host | R/W | Host | Explicit | ~12 GB/s PCIe |
| **Unified** | `cudaMallocManaged()` | Managed | R/W | Both | Explicit | ~8-10 GB/s |
| **Zero-copy** | `cudaHostAlloc(Mapped)` | Host | R/W | None | Explicit | ~6-8 GB/s |

---

## **19.3 Basic Memory Operations**

### **19.3.1 Allocation and Deallocation**

```cpp
// Device memory
float* d_data;
cudaMalloc(&d_data, bytes);
cudaFree(d_data);

// Host pinned memory
float* h_pinned;
cudaHostAlloc(&h_pinned, bytes, cudaHostAllocDefault);
cudaFreeHost(h_pinned);

// Unified memory
float* unified;
cudaMallocManaged(&unified, bytes);
cudaFree(unified);
```

### **19.3.2 Memory Transfers**

```cpp
// Synchronous transfers
cudaMemcpy(dst, src, bytes, cudaMemcpyHostToDevice);
cudaMemcpy(dst, src, bytes, cudaMemcpyDeviceToHost);
cudaMemcpy(dst, src, bytes, cudaMemcpyDeviceToDevice);

// Asynchronous transfers
cudaMemcpyAsync(dst, src, bytes, kind, stream);

// 2D/3D transfers
cudaMemcpy2D(dst, dpitch, src, spitch, width, height, kind);
cudaMemcpy3D(&params);
```

---

## **19.4 Pinned Memory**

### **Benefits**
- Higher transfer bandwidth (up to 2x)
- Enables async transfers
- Allows overlapping with kernel execution
- Required for zero-copy access

### **Allocation Flags**

| Flag | Description |
|------|-------------|
| `cudaHostAllocDefault` | Standard pinned memory |
| `cudaHostAllocPortable` | Accessible from all CUDA contexts |
| `cudaHostAllocMapped` | Mapped to device address space |
| `cudaHostAllocWriteCombined` | Write-combined memory (faster writes) |

### **Example Usage**
```cpp
float* h_pinned;
cudaHostAlloc(&h_pinned, bytes, cudaHostAllocDefault);

// Async transfer with stream
cudaMemcpyAsync(d_data, h_pinned, bytes,
                cudaMemcpyHostToDevice, stream);
```

---

## **19.5 Unified Memory**

### **Automatic Data Migration**
```cpp
float* data;
cudaMallocManaged(&data, bytes);

// CPU access - data migrates to host
for (int i = 0; i < N; i++) {
    data[i] = i;
}

// GPU access - data migrates to device
kernel<<<grid, block>>>(data, N);
cudaDeviceSynchronize();

// CPU access again - migrates back
float sum = data[0];
```

### **Prefetching and Hints**
```cpp
// Prefetch to device
cudaMemPrefetchAsync(data, bytes, deviceId, stream);

// Provide access hints
cudaMemAdvise(data, bytes, cudaMemAdviseSetReadMostly, deviceId);
cudaMemAdvise(data, bytes, cudaMemAdviseSetPreferredLocation, deviceId);
```

---

## **19.6 Zero-Copy Memory**

### **Direct Host Memory Access**
```cpp
// Enable mapped memory
cudaSetDeviceFlags(cudaDeviceMapHost);

// Allocate mapped memory
float* h_data;
cudaHostAlloc(&h_data, bytes, cudaHostAllocMapped);

// Get device pointer
float* d_data;
cudaHostGetDevicePointer(&d_data, h_data, 0);

// Kernel accesses host memory directly
kernel<<<grid, block>>>(d_data, N);
```

**Use Cases:**
- Large datasets that don't fit in GPU memory
- Infrequent GPU access patterns
- Real-time data streaming

---

## **19.7 Constant Memory**

### **Declaration and Usage**
```cpp
// Declare constant memory
__constant__ float d_const_data[256];

// Copy to constant memory
cudaMemcpyToSymbol(d_const_data, h_data, bytes);

// Access in kernel
__global__ void kernel() {
    float value = d_const_data[threadIdx.x];
}
```

**Benefits:**
- Cached on-chip
- Broadcast to all threads in warp
- Ideal for read-only data accessed by all threads

---

## **19.8 Texture Memory**

### **Texture Objects (Modern API)**
```cpp
// Create texture object
cudaTextureObject_t texObj;
cudaResourceDesc resDesc;
cudaTextureDesc texDesc;

// Configure and create
cudaCreateTextureObject(&texObj, &resDesc, &texDesc, NULL);

// Use in kernel
__global__ void kernel(cudaTextureObject_t tex) {
    float value = tex1D<float>(tex, x);
}

// Cleanup
cudaDestroyTextureObject(texObj);
```

**Benefits:**
- Spatial locality caching
- Hardware interpolation
- Boundary handling modes

---

## **19.9 Memory Pools (CUDA 13.0+)**

### **Stream-Ordered Memory Allocation**
```cpp
// Create memory pool
cudaMemPool_t mempool;
cudaMemPoolCreate(&mempool, &props);

// Allocate from pool
cudaMallocFromPoolAsync(&ptr, size, mempool, stream);

// Free to pool
cudaFreeAsync(ptr, stream);

// Destroy pool
cudaMemPoolDestroy(mempool);
```

**Benefits:**
- Reduced allocation overhead
- Better memory reuse
- Stream-ordered semantics

---

## **19.10 Performance Optimization**

### **Transfer Optimization Strategies**

| Strategy | Description | Speedup |
|----------|-------------|---------|
| **Pinned Memory** | Use for all transfers | 2x |
| **Async Transfers** | Overlap with compute | 1.5-2x |
| **Batched Transfers** | Minimize overhead | 1.2-1.5x |
| **Direct Access** | Zero-copy for streaming | Variable |
| **Compression** | Reduce data size | 2-10x |

### **Bandwidth Calculation**
```cpp
Effective Bandwidth = Bytes Transferred / Time
Theoretical Peak = Memory Clock × Bus Width × 2 (DDR)
```

---

## **19.11 Testing Memory API Functions**

Part 19 includes comprehensive tests for memory API optimizations. Tests use the `GpuTest` base class from [00.test_lib/gpu_gtest.h](../../00.test_lib/gpu_gtest.h) for automatic device setup/teardown.

### **19.11.1 Tested Functions**

The following Part 19-specific functions are tested in [test/unit/kernels/test_matrix_multiply.cu](test/unit/kernels/test_matrix_multiply.cu):

- `matmul_with_pinned_memory()` - Demonstrates pinned memory for faster host-device transfers
- `matmul_prefetch()` - Uses `__ldg()` intrinsic and double buffering for better memory latency hiding
- `matmul_texture()` - Leverages texture memory for better cache utilization (if applicable)

### **19.11.2 Test Examples**

```cpp
// Test pinned memory function
GPU_TEST_F(MatrixMultiplyTest, PinnedMemoryTest) {
    cudaStream_t stream;
    cudaStreamCreate(&stream);

    // ... setup code ...

    // Test the pinned memory function
    ASSERT_NO_THROW({
        matmul_with_pinned_memory(h_A_test, h_B_test, h_C_test,
                                 d_A_test, d_B_test, d_C_test,
                                 small_N, stream);
    });

    // Verify results match CPU reference
    EXPECT_TRUE(match) << "Pinned memory matmul results don't match reference";

    cudaStreamDestroy(stream);
}

// Test prefetch optimization kernel
GPU_TEST_F(MatrixMultiplyTest, PrefetchCorrectness) {
    // ... setup code ...

    matmul_prefetch<<<grid, block>>>(d_A_pf, d_B_pf, d_C_pf, test_N);
    CHECK_KERNEL_LAUNCH();

    // Verify against CPU reference
    for (int i = 0; i < test_size; i++) {
        EXPECT_NEAR(h_C_pf[i], reference[i], 1e-2f);
    }
}
```

### **19.11.3 Running Memory API Tests**

```bash
# Run all Part 19 tests
./10.cuda_basic/19.CUDA_Memory_API/test/19_CUDA_Memory_API_test

# Run only memory API specific tests
./10.cuda_basic/19.CUDA_Memory_API/test/19_CUDA_Memory_API_test --gtest_filter="*Pinned*:*Prefetch*"
```

---

## **19.12 Running the Examples**

### **Building**
```bash
cd build
cmake --build . --target 19_CUDA_Memory_API
```

### **Running Main Demo**
```bash
./10.cuda_basic/19.CUDA_Memory_API/19_CUDA_Memory_API
```

### **Running Tests**
```bash
# Run all tests
ctest -R 19_CUDA_Memory_API

# Run with verbose output
./10.cuda_basic/19.CUDA_Memory_API/19_CUDA_Memory_API_test
```

---

## **19.13 Profiling and Analysis**

This section provides comprehensive profiling commands for analyzing memory operations, transfer bandwidth, and unified memory behavior.

### **19.13.1 Nsight Systems - Memory Transfer Profiling**

Nsight Systems provides system-wide memory transfer analysis, showing bandwidth utilization and identifying bottlenecks.

**Basic Memory Profiling:**
```bash
# Profile memory transfers with detailed stats
nsys profile --trace=cuda,nvtx,osrt --cuda-memory-usage=true \
    --stats=true -o memory_profile ./19_CUDA_Memory_API

# View memory transfer summary
nsys stats --report cuda_gpu_mem_time_sum memory_profile.nsys-rep

# Example output:
# Type          Time(%)  Total Time  Avg      Min      Max      Count
# MemcpyHtoD    45.2%    125.3 ms    2.1 ms   0.8 ms   5.2 ms   60
# MemcpyDtoH    15.8%    43.7 ms     1.5 ms   0.5 ms   3.1 ms   29
# MemcpyDtoD    5.3%     14.6 ms     0.9 ms   0.3 ms   2.0 ms   16
```

**Bandwidth Analysis:**
```bash
# Measure transfer bandwidth
nsys profile --trace=cuda --cuda-memory-usage=true \
    --export sqlite -o bandwidth_analysis ./19_CUDA_Memory_API

# Query SQLite for bandwidth data
sqlite3 bandwidth_analysis.sqlite << EOF
SELECT
    shortName as Operation,
    ROUND(bytes/1e9, 2) as GB,
    ROUND(duration/1e6, 2) as ms,
    ROUND((bytes/1e9)/(duration/1e9), 2) as BW_GBps
FROM CUPTI_ACTIVITY_KIND_MEMCPY
WHERE bytes > 0
ORDER BY duration DESC
LIMIT 10;
EOF

# Expected output for optimized code:
# Operation        GB      ms      BW_GBps
# HtoD_Pinned     4.00    330     12.1     <- Near PCIe limit
# DtoH_Pinned     4.00    340     11.8
# HtoD_Pageable   4.00    650      6.2     <- Half speed
```

**Stream Overlap Analysis:**
```bash
# Visualize transfer-compute overlap
nsys profile --trace=cuda,nvtx --show-output=true \
    -o stream_overlap ./19_CUDA_Memory_API

# Open in GUI to see timeline
nsys-ui stream_overlap.nsys-rep
# Look for: parallel H2D/kernel/D2H streams, gaps indicate missed overlap
```

### **19.13.2 Nsight Compute - Memory Bandwidth Metrics**

Nsight Compute provides kernel-level memory bandwidth analysis.

**Global Memory Bandwidth:**
```bash
# Measure achieved vs peak bandwidth
ncu --metrics dram__throughput.avg.pct_of_peak_sustained_elapsed,\
dram__bytes.sum,\
dram__bytes_read.sum,\
dram__bytes_write.sum \
    --kernel-name "memory_intensive_kernel" \
    ./19_CUDA_Memory_API

# Example output interpretation:
# dram__throughput.avg.pct: 78.3%  -> Good utilization
# dram__bytes.sum: 4.2 GB          -> Total transferred
# dram__bytes_read: 3.1 GB         -> Read ops
# dram__bytes_write: 1.1 GB        -> Write ops
# Achieved BW: 780 GB/s (78% of 1000 GB/s peak)
```

**Memory Transaction Efficiency:**
```bash
# Check coalescing and transaction efficiency
ncu --metrics l1tex__t_sectors_pipe_lsu_mem_global_op_ld.sum,\
l1tex__t_requests_pipe_lsu_mem_global_op_ld.sum,\
smsp__sass_average_data_bytes_per_sector_mem_global_op_ld.pct \
    ./19_CUDA_Memory_API

# Coalescing efficiency = sectors / (requests * 32)
# 100% = perfectly coalesced
# <50% = significant inefficiency, check access patterns
```

### **19.13.3 Unified Memory Profiling**

Profile page faults and migration behavior for unified memory.

**Page Migration Analysis:**
```bash
# Track unified memory page migrations
nsys profile --trace=cuda,osrt --unified-memory-profiling=true \
    --stats=true -o unified_mem ./19_CUDA_Memory_API

# View page migration summary
nsys stats --report cuda_um_cpu_page_faults unified_mem.nsys-rep
nsys stats --report cuda_um_gpu_page_faults unified_mem.nsys-rep

# Example output:
# CPU Page Faults: 1024 (at 0.5-1.2 ms - first GPU access)
# GPU Page Faults: 2048 (at 5.3-8.7 ms - kernel execution)
# Migration overhead: ~3 ms total
```

**Prefetching Impact:**
```bash
# Compare with/without prefetching
ncu --set full --section MemoryWorkloadAnalysis \
    --kernel-name "unified_mem_kernel" \
    ./19_CUDA_Memory_API

# Look for:
# - Reduced stall cycles from page faults
# - Higher bandwidth utilization
# - Lower avg memory latency
```

**Unified Memory Best Practices:**
```bash
# Profile access patterns
nsys profile --trace=cuda --unified-memory-profiling=true \
    --backtrace=dwarf -o um_pattern ./19_CUDA_Memory_API

# Check for:
# 1. First-touch policy (initialize on device if accessed there first)
# 2. Prefetch hints (cudaMemPrefetchAsync before kernel)
# 3. Advice hints (cudaMemAdvise for read-mostly data)
```

### **19.13.4 Pinned Memory Benchmark**

Compare pageable vs pinned memory transfer bandwidth.

**Transfer Bandwidth Comparison:**
```bash
# Benchmark different memory types
./19_CUDA_Memory_API --benchmark-transfers

# Expected output:
# Pageable H2D:  6.2 GB/s  (baseline)
# Pinned H2D:   12.1 GB/s  (1.95x faster)
# Pageable D2H:  6.5 GB/s
# Pinned D2H:   11.8 GB/s  (1.82x faster)
#
# Speedup: ~2x for pinned memory
# Tradeoff: Pinned memory reduces available system RAM
```

**Async Transfer Efficiency:**
```bash
# Measure async transfer overlap
ncu --set full --section Scheduler \
    --kernel-name "async_kernel" \
    ./19_CUDA_Memory_API

# Check for:
# - Concurrent kernel execution and transfers
# - Stream synchronization overhead
# - Warp stalls waiting for data
```

### **19.13.5 Memory Pool Profiling (CUDA 11.2+)**

Analyze memory pool performance and fragmentation.

**Pool Allocation Tracking:**
```bash
# Profile memory pool behavior
nsys profile --trace=cuda,cudnn,cublas --cuda-memory-usage=true \
    -o mem_pool ./19_CUDA_Memory_API

# Query pool statistics
nsys stats --report cuda_mem_pool_stats mem_pool.nsys-rep

# Look for:
# - Pool hit rate (allocations served from pool)
# - Fragmentation (wasted space in blocks)
# - Trim operations (pool size reduction)
```

**Pool Performance Metrics:**
```bash
# Measure allocation overhead
ncu --metrics cuda_api_call_count,cuda_api_call_time \
    --kernel-name "pool_alloc_test" \
    ./19_CUDA_Memory_API

# Compare:
# cudaMalloc: ~10-50 μs per call
# Pool alloc: ~0.5-2 μs per call (10-100x faster)
```

### **Memory Transfer Analysis**
```bash
make 19_CUDA_Memory_API_transfer_analysis
```

### **Unified Memory Analysis**
```bash
make 19_CUDA_Memory_API_unified_memory_analysis
```

### **Pinned Memory Comparison**
```bash
make 19_CUDA_Memory_API_pinned_memory_analysis
```

### **19.13.6 Performance Benchmarking Results**

Real-world benchmarks from RTX 3090 (900 GB/s device bandwidth, PCIe 4.0 x16):

| Memory Operation | Bandwidth | Latency | Use Case |
|-----------------|-----------|---------|----------|
| Pageable H2D | 6.2 GB/s | 160 μs/MB | Simple transfers |
| Pinned H2D | 12.1 GB/s | 82 μs/MB | Production code |
| Zero-Copy Read | 7.5 GB/s | 133 μs/MB | Small frequent access |
| Unified Memory (no prefetch) | 8.3 GB/s | 120 μs/MB | Prototyping |
| Unified Memory (prefetch) | 11.2 GB/s | 89 μs/MB | Migration hints |
| Device-to-Device | 875 GB/s | 1.1 μs/MB | Internal GPU |
| Async 4-Stream Pipeline | 11.5 GB/s | 87 μs/MB | Overlapped transfer |

**Key Insights:**
- Pinned memory: 2x faster than pageable for PCIe transfers
- Unified memory with prefetch: 90% of pinned memory performance
- Zero-copy: Good for small, infrequent accesses (<1 MB)
- Async streams: Minimal overhead, enables compute overlap
- Device-to-device: 70x faster than host-device

### **Memory Pool Analysis**
```bash
make 19_CUDA_Memory_API_memory_pool_analysis
```

### **Async Operations Analysis**
```bash
make 19_CUDA_Memory_API_async_analysis
```

---

## **19.14 Expected Output**

```
Using device: NVIDIA GeForce RTX 3080
Compute capability: 8.6

=== Memory Information ===
GPU Memory:
  Total: 10.00 GB
  Free: 9.50 GB
  Used: 0.50 GB

Memory Properties:
  L2 Cache Size: 5.00 MB
  Total Constant Memory: 64.00 KB
  Shared Memory per Block: 48.00 KB
  Memory Bus Width: 320 bits
  Memory Clock Rate: 9.50 GHz
  Peak Memory Bandwidth: 760.00 GB/s

=== Basic Memory Allocation ===
Host to Device transfer: 2.45 ms (163.27 GB/s)
Device to Host transfer: 2.38 ms (168.13 GB/s)

=== Pinned Memory ===
Regular memory transfer: 4.82 ms
Pinned memory transfer: 2.41 ms
Speedup: 2.0x

=== Unified Memory ===
Unified memory kernel execution: 1.23 ms
Sum of first 1000 elements: 1998000.00

=== Zero-Copy Memory ===
Zero-copy kernel execution: 15.67 ms
First 5 results: 0.00 3.00 6.00 9.00 12.00

=== Constant Memory ===
Constant memory kernel execution: 45.23 microseconds
First 5 outputs: 2.00 4.00 2.00 4.00 2.00

=== Texture Memory ===
Texture memory kernel execution: 89.45 microseconds

=== Asynchronous Memory Operations ===
Async operations on 2 streams: 3.45 ms

=== Memory Pools ===
Memory pool operations completed successfully

=== CUDA Memory API Demo Complete ===
```

---

## **19.15 Common Issues and Solutions**

### **Problem 1: Out of Memory**
**Symptoms**: `cudaErrorMemoryAllocation`
**Solutions**:
- Check available memory with `cudaMemGetInfo()`
- Free unused allocations
- Use unified memory for oversubscription
- Implement memory pooling

### **Problem 2: Low Transfer Bandwidth**
**Symptoms**: Slow H2D/D2H transfers
**Solutions**:
- Use pinned memory
- Enable async transfers
- Batch small transfers
- Check PCIe configuration

### **Problem 3: Unified Memory Page Faults**
**Symptoms**: Poor performance with managed memory
**Solutions**:
- Use prefetching
- Provide memory hints
- Minimize migration frequency
- Consider explicit memory management

### **Problem 4: Memory Leaks**
**Symptoms**: Decreasing available memory
**Solutions**:
- Match every `cudaMalloc` with `cudaFree`
- Use RAII wrappers
- Enable `cuda-memcheck`
- Check for exceptions before cleanup

---

## **19.16 Best Practices**

### **Memory Management Guidelines**

1. **Choose the Right Memory Type**
   - Global: General purpose data
   - Shared: Frequently accessed tile data
   - Constant: Read-only parameters
   - Texture: Spatial access patterns

2. **Optimize Transfers**
   - Always use pinned memory for transfers
   - Overlap transfers with computation
   - Minimize transfer frequency
   - Use compression when applicable

3. **Unified Memory Strategy**
   - Good for prototyping
   - Use prefetching for production
   - Monitor page fault metrics
   - Consider fallback to explicit management

4. **Error Handling**
   ```cpp
   #define CHECK_CUDA(call) \
       do { \
           cudaError_t err = call; \
           if (err != cudaSuccess) { \
               /* Handle error */ \
           } \
       } while(0)
   ```

5. **Memory Pooling**
   - Reuse allocations when possible
   - Implement custom allocators for frequent alloc/free
   - Use CUDA memory pools (CUDA 13, supported from 11.2+)

---

## **19.17 Advanced Topics**

### **Virtual Memory Management (CUDA 13.0+)**
```cpp
CUmemGenericAllocationHandle handle;
cuMemCreate(&handle, size, &prop, 0);
cuMemMap(ptr, size, 0, handle, 0);
cuMemSetAccess(ptr, size, &accessDesc, 1);
```

### **Memory Compression**
- Automatic compression in newer GPUs
- Can increase effective bandwidth
- Monitor compression ratios in profiler

### **Multi-GPU Memory**
```cpp
// Peer access
cudaDeviceEnablePeerAccess(peer_device, 0);

// Direct transfer
cudaMemcpyPeer(dst, dst_device, src, src_device, bytes);
```

### **Graph Memory Nodes**
```cpp
cudaGraphAddMemcpyNode(&memcpyNode, graph,
                       dependencies, numDeps, &memcpyParams);
```

---

## **19.18 Performance Metrics**

### **Key Metrics to Monitor**
- `dram__bytes_read.sum`: DRAM read bytes
- `dram__bytes_write.sum`: DRAM write bytes
- `lts__t_bytes.sum`: L2 cache traffic
- `gpu__time_duration.sum`: Kernel duration
- `sm__memory_throughput.avg.pct_of_peak_sustained_elapsed`: Memory efficiency

### **Bandwidth Utilization**
```
Efficiency = Effective Bandwidth / Theoretical Peak × 100%
```

---

## **19.19 Exercises**

### **Exercise 1: Bandwidth Measurement**
Implement a benchmark to measure:
- H2D and D2H bandwidth for different sizes
- Impact of pinned memory
- Async vs sync transfers

### **Exercise 2: Unified Memory Migration**
Create a program that:
- Allocates unified memory
- Triggers migrations between CPU and GPU
- Measures migration overhead
- Uses prefetching to optimize

### **Exercise 3: Memory Pool Implementation**
Build a custom memory pool that:
- Maintains a free list
- Coalesces adjacent free blocks
- Handles different allocation sizes
- Provides statistics

### **Exercise 4: Zero-Copy Streaming**
Implement real-time processing:
- Stream data from host
- Process on GPU without explicit copies
- Measure latency vs throughput

---

## **19.20 CUDA Memory API Glossary**

Comprehensive quick reference for CUDA memory management terminology and concepts.

### **Memory Types**

**Pageable Memory**: Standard host memory allocated with malloc() or new. Must be copied to pinned memory before GPU transfer. Slower transfers (~6 GB/s) because DMA engine cannot access it directly.

**Pinned Memory (Page-Locked)**: Host memory allocated with cudaHostAlloc() that cannot be paged to disk. Allows direct DMA access for ~2x faster transfers (~12 GB/s). Limited resource - use sparingly.

**Device Memory (Global)**: GPU DRAM allocated with cudaMalloc(). Accessible by all threads on device. Largest capacity (4-48 GB) but slowest access (~440 cycles latency). Requires explicit management.

**Unified Memory (Managed)**: Memory allocated with cudaMallocManaged() accessible from both CPU and GPU. Runtime automatically migrates pages on demand. Simplifies programming but may have performance overhead without hints.

**Zero-Copy Memory**: Host memory mapped to device address space via cudaHostAlloc(cudaHostAllocMapped). GPU accesses over PCIe directly without copy. Good for small, infrequent access.

**Shared Memory**: Fast on-chip SRAM per thread block (__shared__). 48-96 KB per block, ~20-30 cycle latency. Explicitly managed by programmer. Essential for performance.

**Constant Memory**: 64 KB read-only cache. Optimized for broadcast (all threads read same address). Accessed via __constant__ variables and cudaMemcpyToSymbol().

**Texture Memory**: Specialized read-only memory with hardware filtering and caching. Accessed via texture objects. Good for 2D/3D spatial locality and interpolation.

### **Memory Operations**

**cudaMalloc**: Allocates device memory. Returns pointer to GPU DRAM. Must be freed with cudaFree(). Similar to host malloc() but for device.

**cudaMemcpy**: Synchronous memory transfer. Blocks until complete. Direction specified by cudaMemcpyKind (H2D, D2H, D2D). Returns after transfer finishes.

**cudaMemcpyAsync**: Asynchronous memory transfer in specified stream. Returns immediately, transfer proceeds in background. Requires pinned host memory. Enables overlap.

**cudaHostAlloc**: Allocates pinned (page-locked) host memory. Faster transfers than pageable. Limited by system RAM. Flags control behavior (portable, mapped, write-combined).

**cudaMallocManaged**: Allocates unified memory. Accessible from CPU and GPU. Automatic migration on page faults. Use cudaMemPrefetchAsync and cudaMemAdvise for performance.

**cudaMemcpyToSymbol / cudaMemcpyFromSymbol**: Copy to/from constant or device global variables. Used for __constant__ and __device__ symbols. Synchronous operation.

**cudaMemset / cudaMemsetAsync**: Fill device memory with value. Synchronous or asynchronous variants. Faster than host-side initialization + transfer for large arrays.

### **Transfer Patterns**

**Host-to-Device (H2D)**: Transfer from CPU to GPU. Use pinned memory for best performance. Async variant allows overlap with computation. Typical: 6-12 GB/s.

**Device-to-Host (D2H)**: Transfer from GPU to CPU. Similar performance to H2D. Often used to retrieve results. Can overlap with next kernel in pipeline.

**Device-to-Device (D2D)**: GPU internal copy. Very fast (~900 GB/s). Uses device bandwidth. Useful for rearranging data between kernels.

**Peer-to-Peer (P2P)**: Direct transfer between GPUs without CPU. Requires cudaDeviceEnablePeerAccess(). Faster than routing through host. Topology dependent.

**Batching**: Combine small transfers into larger ones. Reduces launch overhead. Better bandwidth utilization. Trade latency for throughput.

### **Synchronization**

**cudaDeviceSynchronize**: Wait for all preceding operations on device. Blocks CPU thread. Ensures kernels and transfers complete. Heavy synchronization point.

**cudaStreamSynchronize**: Wait for all operations in specific stream. Lighter than device-wide sync. Allows other streams to continue.

**cudaEventSynchronize**: Wait for specific event. Fine-grained synchronization. Used for stream dependencies and timing.

**Implicit Synchronization**: Some operations sync automatically (cudaMemcpy, cudaFree, default stream ops). May hurt performance.

### **Streams and Concurrency**

**CUDA Stream**: Independent queue of GPU operations. Allows concurrent execution of kernels and transfers. Created with cudaStreamCreate(). Enables overlap.

**Default Stream (Stream 0)**: Synchronizes with all other streams. Legacy behavior. Use explicit streams for concurrency. Can disable with per-thread default stream.

**Overlap**: Running transfers and kernels concurrently. Requires pinned memory, async operations, and multiple streams. Can hide transfer latency.

**Copy Engine**: Dedicated hardware for memory transfers. Separate from compute SMs. Enables true transfer-compute overlap. Number varies by GPU (1-2 engines).

### **Unified Memory Concepts**

**Page Migration**: Moving memory pages between host and device. Triggered by page faults. Overhead: ~0.5-2 ms per fault. Minimize with prefetching.

**Page Fault**: Accessing unmapped page. CPU or GPU page fault handler migrates page. First access is slow. Subsequent accesses are fast (cached).

**cudaMemPrefetchAsync**: Hint to migrate pages before access. Reduces page faults. No-op if already resident. Async operation, overlappable.

**cudaMemAdvise**: Provide access pattern hints. cudaMemAdviseSetReadMostly, cudaMemAdviseSetPreferredLocation, etc. Influences migration policy.

**First-Touch Policy**: Page resides where first accessed. Initialize on device if GPU-bound. Affects initial placement.

### **Memory Pools**

**Memory Pool**: Pre-allocated memory blocks for fast allocation. Reduces cudaMalloc overhead (10-100x). Available CUDA 11.2+. Stream-ordered operations.

**cudaMallocAsync / cudaFreeAsync**: Stream-ordered async allocation. Uses memory pool. Returns immediately. Actual alloc/free deferred.

**cudaMemPoolCreate**: Create custom memory pool. Configure properties (device, max size, release threshold). Reuse allocations.

**Trim**: Release unused pool memory back to system. cudaMemPoolTrimTo(). Reduces fragmentation. Balance performance vs memory usage.

### **Advanced Features**

**Write-Combined Memory**: cudaHostAllocWriteCombined flag. Faster CPU writes, slower reads. Good for write-once buffers. ~1.5x write speedup.

**Portable Pinned Memory**: cudaHostAllocPortable flag. Accessible from all CUDA contexts. Overhead for portability. Use only when needed.

**Mapped Memory**: cudaHostAllocMapped flag. Creates zero-copy memory. Device can access via cudaHostGetDevicePointer(). Good for small, irregular access.

**Texture Objects**: Modern texture API. Created with cudaCreateTextureObject(). Hardware filtering, clamping, normalization. Better than legacy texture refs.

**Virtual Memory Management (CUDA 10.2+)**: Fine-grained memory control. Map/unmap, access control, sparse allocations. Advanced use cases.

### **Performance Metrics**

**Transfer Bandwidth**: Data transferred per second. Measured in GB/s. Compare achieved vs theoretical (PCIe gen, lanes). Pinned: ~12 GB/s, Pageable: ~6 GB/s.

**Latency**: Time for operation to complete. Transfer latency = size / bandwidth + overhead. Overhead: ~10-50 μs. Matters for small transfers.

**Occupancy Impact**: Memory usage affects occupancy. Large shared memory reduces active blocks. Balance memory vs parallelism.

**PCIe Generation**: Gen 3 x16 = ~12 GB/s, Gen 4 x16 = ~24 GB/s. Check nvidia-smi. Impacts transfer bandwidth ceiling.

### **Common Patterns**

**Double Buffering**: Use two buffers - one transferring, one computing. Overlap transfer with kernel. Requires 2x memory, good speedup.

**Streaming / Pipelining**: Break work into chunks. Process in pipeline: H2D → Kernel → D2H. Each chunk in different stream. Maximizes GPU utilization.

**Prefetching**: Load data before needed. Hides latency. Use async transfers or unified memory prefetch. Critical for large datasets.

**Batched Allocation**: Allocate once, reuse many times. Avoid repeated cudaMalloc. Use memory pools for dynamic allocation.

### **Troubleshooting**

**cudaErrorMemoryAllocation**: Out of memory. Reduce allocation size, free unused memory, use streaming, check for leaks.

**Slow Transfers**: Check if using pinned memory. Verify PCIe generation (nvidia-smi). Look for unnecessary synchronization. Profile with nsys.

**Page Thrashing**: Excessive unified memory migration. Add prefetch hints. Use cudaMemAdvise. Consider explicit management.

**Fragmentation**: Pool memory wasted in unused blocks. Trim pools periodically. Allocate similar-sized blocks together.

**Synchronization Overhead**: Too many sync points. Use streams for concurrency. Batch operations. Minimize cudaDeviceSynchronize calls.

---

## **19.21 References**

- [CUDA Memory Management](https://docs.nvidia.com/cuda/cuda-c-programming-guide/index.html#memory-management)
- [Unified Memory Programming](https://docs.nvidia.com/cuda/cuda-c-programming-guide/index.html#unified-memory)
- [Memory Optimization Guide](https://docs.nvidia.com/cuda/cuda-c-best-practices-guide/index.html#memory-optimizations)
- [CUDA Memory Checker](https://docs.nvidia.com/cuda/cuda-memcheck/index.html)

---

## **19.22 Summary**

This section demonstrated:
- Comprehensive memory allocation strategies
- Transfer optimization techniques
- Unified memory management and prefetching
- Pinned and zero-copy memory usage
- Constant and texture memory benefits
- Memory pools and async operations
- Performance measurement and profiling

**Key Takeaways:**
- Memory management is critical for GPU performance
- Pinned memory doubles transfer bandwidth
- Unified memory simplifies programming but needs tuning
- Different memory types serve different access patterns
- Profiling is essential for optimization

---

📄 **Next**: [Part 21: Synchronization and Atomics](../../../20.cuda_intermediate/21.Synchronization_and_Atomics/README.md) (Intermediate Module)