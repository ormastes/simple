# 🎯 Part 41: Advanced PTX Assembly
**Goal**: Master low-level GPU programming with inline PTX assembly for performance-critical code sections and hardware-specific optimizations.

## Project Structure
```
41.Advanced_PTX_Assembly/
├── README.md          - This documentation
├── CMakeLists.txt     - Build configuration
├── src/               - Source implementations
│   ├── kernels/       - PTX inline assembly kernels
│   │   ├── inline_ptx.cu       - Basic inline PTX operations
│   │   ├── ptx_atomics.cu      - Atomic operations with PTX
│   │   └── warp_primitives.cu  - Warp-level PTX operations
│   └── part_specific/ - Demo executables
│       └── ptx_demo.cu         - Demonstration program
└── test/              - Test files
    └── unit/
        └── kernels/   - Tests for PTX kernels
            ├── test_inline_ptx.cu
            ├── test_ptx_atomics.cu
            └── test_warp_primitives.cu
```

## Quick Navigation
- [41.1 Introduction to PTX](#411-introduction-to-ptx)
- [41.2 PTX Syntax and Structure](#412-ptx-syntax-and-structure)
- [41.3 Inline PTX in CUDA](#413-inline-ptx-in-cuda)
- [41.4 Memory Operations with PTX](#414-memory-operations-with-ptx)
- [41.5 Atomic Operations](#415-atomic-operations)
- [41.6 Warp-Level Operations](#416-warp-level-operations)
- [41.7 PTX Generation and Analysis](#417-ptx-generation-and-analysis)
- [41.8 Testing](#418-testing)
- [41.9 Summary](#419-summary)

---

## **41.1 Introduction to PTX**

PTX (Parallel Thread Execution) is CUDA's virtual assembly language that provides low-level control over GPU operations while maintaining forward compatibility across GPU generations. Understanding PTX enables fine-grained optimization of performance-critical code sections.

### **41.1.1 What is PTX?**

PTX serves as an intermediate representation in the CUDA compilation pipeline:
- Virtual instruction set architecture (ISA) for NVIDIA GPUs
- Platform-independent representation compiled to device-specific SASS
- Provides forward compatibility across GPU architectures
- Enables low-level optimizations not accessible through CUDA C++

**Key Benefits:**
- Direct access to hardware features
- Explicit control over memory access patterns
- Reduced instruction overhead in critical sections
- Access to special registers and operations

### **41.1.2 PTX in the Compilation Flow**

```
CUDA C++ Source (.cu)
        ↓
    [nvcc frontend]
        ↓
    PTX Code (.ptx)
        ↓
    [ptxas assembler]
        ↓
    SASS (GPU-specific machine code)
        ↓
    Executable Binary
```

---

## **41.2 PTX Syntax and Structure**

PTX uses a simple, readable syntax similar to assembly language. This section covers the fundamental syntax elements.

### **41.2.1 Basic PTX Syntax**

PTX programs consist of directives and instructions:

```ptx
.version 7.0                    // PTX version
.target sm_80                   // Target architecture
.address_size 64                // 64-bit addressing

// Function declaration
.entry my_kernel(
    .param .u64 param_ptr,      // Pointer parameter
    .param .u32 param_size      // Integer parameter
) {
    // Register declarations
    .reg .u32 %r<10>;           // 10 32-bit integer registers
    .reg .u64 %rd<5>;           // 5 64-bit registers
    .reg .f32 %f<4>;            // 4 32-bit float registers
    .reg .pred %p<3>;           // 3 predicate registers

    // Load parameters
    ld.param.u64 %rd1, [param_ptr];
    ld.param.u32 %r1, [param_size];

    // Instructions
    mov.u32 %r2, %tid.x;        // Get thread ID
    add.u32 %r3, %r2, %r1;      // Add operation

    // Store result
    st.global.u32 [%rd1], %r3;

    ret;                        // Return
}
```

### **41.2.2 PTX Data Types**

| Type | Description | Example |
|------|-------------|---------|
| `.u8`, `.u16`, `.u32`, `.u64` | Unsigned integers | `.reg .u32 %r1;` |
| `.s8`, `.s16`, `.s32`, `.s64` | Signed integers | `.reg .s32 %r2;` |
| `.f16`, `.f32`, `.f64` | Floating point | `.reg .f32 %f1;` |
| `.b8`, `.b16`, `.b32`, `.b64` | Untyped bits | `.reg .b32 %b1;` |
| `.pred` | Predicate (boolean) | `.reg .pred %p1;` |

---

## **41.3 Inline PTX in CUDA**

Inline PTX allows embedding PTX instructions directly in CUDA C++ code using the `asm` keyword. This provides low-level control while maintaining the structure of CUDA programs.

### **41.3.1 Basic Inline Assembly Syntax**

The inline PTX syntax follows the extended asm format:

```cuda
asm("ptx_instruction"
    : output_operands       // Output constraints
    : input_operands        // Input constraints
    : clobbered_registers   // Modified registers (optional)
);
```

**Example - Simple Addition:**

```cuda
// src/kernels/inline_ptx.cu
__device__ int add_ptx(int a, int b) {
    int result;
    asm("add.s32 %0, %1, %2;"
        : "=r"(result)      // Output: %0 in register
        : "r"(a), "r"(b)    // Inputs: %1, %2 in registers
    );
    return result;
}
```

**Constraint Modifiers:**
- `"=r"` - Output in register (write-only)
- `"r"` - Input in register (read-only)
- `"+r"` - Read-write register
- `"l"` - 64-bit register (for pointers)
- `"f"` - Floating-point register
- `"d"` - Double-precision floating-point register

### **41.3.2 Arithmetic and Logical Operations**

Inline PTX is useful for operations that benefit from explicit instruction selection:

```cuda
// src/kernels/inline_ptx.cu
__device__ float fma_ptx(float a, float b, float c) {
    float result;
    // Fused multiply-add: result = a * b + c
    asm("fma.rn.f32 %0, %1, %2, %3;"
        : "=f"(result)
        : "f"(a), "f"(b), "f"(c)
    );
    return result;
}

__device__ int popc_ptx(unsigned int x) {
    int result;
    // Population count (count set bits)
    asm("popc.b32 %0, %1;"
        : "=r"(result)
        : "r"(x)
    );
    return result;
}

__device__ int bfind_ptx(unsigned int x) {
    int result;
    // Find first set bit (most significant)
    asm("bfind.u32 %0, %1;"
        : "=r"(result)
        : "r"(x)
    );
    return result;
}
```

Source: `src/kernels/inline_ptx.cu:8-35`

### **41.3.3 Bit Manipulation**

PTX provides efficient bit manipulation instructions:

```cuda
// src/kernels/inline_ptx.cu
__device__ int reverse_bits_ptx(int x) {
    int result;
    // Reverse all 32 bits
    asm("brev.b32 %0, %1;"
        : "=r"(result)
        : "r"(x)
    );
    return result;
}

__device__ int byte_perm_ptx(int a, int b, int selector) {
    int result;
    // Arbitrary byte permutation
    asm("prmt.b32 %0, %1, %2, %3;"
        : "=r"(result)
        : "r"(a), "r"(b), "r"(selector)
    );
    return result;
}

__device__ unsigned int clz_ptx(unsigned int x) {
    unsigned int result;
    // Count leading zeros
    asm("clz.b32 %0, %1;"
        : "=r"(result)
        : "r"(x)
    );
    return result;
}
```

Source: `src/kernels/inline_ptx.cu:37-65`

---

## **41.4 Memory Operations with PTX**

PTX allows fine-grained control over memory operations including cache hints and access patterns.

### **41.4.1 Memory Access with Cache Control**

PTX provides cache modifiers to optimize memory access patterns:

```cuda
// src/kernels/inline_ptx.cu
__device__ void prefetch_l1_ptx(const void* ptr) {
    // Prefetch data into L1 cache
    asm volatile("prefetch.global.L1 [%0];"
        :
        : "l"(ptr)
    );
}

__device__ void prefetch_l2_ptx(const void* ptr) {
    // Prefetch data into L2 cache
    asm volatile("prefetch.global.L2 [%0];"
        :
        : "l"(ptr)
    );
}

__device__ float load_streaming_ptx(const float* src) {
    float val;
    // Load with streaming cache hint (cache at global level only)
    asm("ld.global.cs.f32 %0, [%1];"
        : "=f"(val)
        : "l"(src)
    );
    return val;
}

__device__ void store_streaming_ptx(float* dst, float val) {
    // Store with streaming cache hint
    asm volatile("st.global.cs.f32 [%0], %1;"
        :
        : "l"(dst), "f"(val)
    );
}
```

**Cache Modifiers:**
- `.ca` - Cache at all levels (default)
- `.cg` - Cache at global level (L2)
- `.cs` - Cache streaming (evict first)
- `.lu` - Last use hint
- `.cv` - Don't cache, volatile

Source: `src/kernels/inline_ptx.cu:67-100`

### **41.4.2 Volatile Memory Access**

For memory that may be modified by other threads or hardware:

```cuda
// src/kernels/inline_ptx.cu
__device__ int load_volatile_ptx(const int* addr) {
    int result;
    // Volatile load ensures fresh read
    asm volatile("ld.global.volatile.s32 %0, [%1];"
        : "=r"(result)
        : "l"(addr)
    );
    return result;
}

__device__ void store_volatile_ptx(int* addr, int val) {
    // Volatile store ensures immediate write
    asm volatile("st.global.volatile.s32 [%0], %1;"
        :
        : "l"(addr), "r"(val)
    );
}
```

Source: `src/kernels/inline_ptx.cu:102-120`

---

## **41.5 Atomic Operations**

PTX atomic operations provide fine control over synchronization and memory ordering.

### **41.5.1 Basic Atomic Operations**

```cuda
// src/kernels/ptx_atomics.cu
__device__ int atomic_add_ptx(int* addr, int val) {
    int old;
    asm volatile("atom.global.add.s32 %0, [%1], %2;"
        : "=r"(old)
        : "l"(addr), "r"(val)
        : "memory"
    );
    return old;
}

__device__ int atomic_min_ptx(int* addr, int val) {
    int old;
    asm volatile("atom.global.min.s32 %0, [%1], %2;"
        : "=r"(old)
        : "l"(addr), "r"(val)
        : "memory"
    );
    return old;
}

__device__ int atomic_max_ptx(int* addr, int val) {
    int old;
    asm volatile("atom.global.max.s32 %0, [%1], %2;"
        : "=r"(old)
        : "l"(addr), "r"(val)
        : "memory"
    );
    return old;
}
```

Source: `src/kernels/ptx_atomics.cu:5-35`

### **41.5.2 Atomic Compare-and-Swap**

```cuda
// src/kernels/ptx_atomics.cu
__device__ int atomic_cas_ptx(int* addr, int compare, int val) {
    int old;
    asm volatile("atom.global.cas.b32 %0, [%1], %2, %3;"
        : "=r"(old)
        : "l"(addr), "r"(compare), "r"(val)
        : "memory"
    );
    return old;
}

// Lock-free increment using CAS
__device__ int atomic_inc_lock_free_ptx(int* addr, int limit) {
    int old, assumed;
    do {
        assumed = *addr;
        old = atomic_cas_ptx(addr, assumed, (assumed + 1) % limit);
    } while (assumed != old);
    return old;
}
```

Source: `src/kernels/ptx_atomics.cu:37-58`

### **41.5.3 Atomic Operations on Shared Memory**

```cuda
// src/kernels/ptx_atomics.cu
__device__ int atomic_add_shared_ptx(int* addr, int val) {
    int old;
    asm volatile("atom.shared.add.s32 %0, [%1], %2;"
        : "=r"(old)
        : "r"(addr), "r"(val)  // Note: "r" not "l" for shared memory
        : "memory"
    );
    return old;
}

__device__ unsigned long long atomic_add_u64_ptx(unsigned long long* addr,
                                                  unsigned long long val) {
    unsigned long long old;
    asm volatile("atom.global.add.u64 %0, [%1], %2;"
        : "=l"(old)
        : "l"(addr), "l"(val)
        : "memory"
    );
    return old;
}
```

Source: `src/kernels/ptx_atomics.cu:60-82`

---

## **41.6 Warp-Level Operations**

Warp-level PTX operations enable efficient thread communication and reduction without shared memory.

### **41.6.1 Warp Shuffle Operations**

Shuffle operations allow threads in a warp to exchange data directly:

```cuda
// src/kernels/warp_primitives.cu
__device__ int shfl_down_ptx(int val, unsigned int delta) {
    int result;
    // Shuffle down: get value from lane (threadIdx.x + delta)
    asm("shfl.sync.down.b32 %0, %1, %2, 0x1f, 0xffffffff;"
        : "=r"(result)
        : "r"(val), "r"(delta)
    );
    return result;
}

__device__ int shfl_up_ptx(int val, unsigned int delta) {
    int result;
    // Shuffle up: get value from lane (threadIdx.x - delta)
    asm("shfl.sync.up.b32 %0, %1, %2, 0x0, 0xffffffff;"
        : "=r"(result)
        : "r"(val), "r"(delta)
    );
    return result;
}

__device__ int shfl_xor_ptx(int val, unsigned int mask) {
    int result;
    // Shuffle XOR: get value from lane (threadIdx.x ^ mask)
    asm("shfl.sync.bfly.b32 %0, %1, %2, 0x1f, 0xffffffff;"
        : "=r"(result)
        : "r"(val), "r"(mask)
    );
    return result;
}
```

Source: `src/kernels/warp_primitives.cu:5-35`

### **41.6.2 Warp Vote Operations**

Vote operations gather boolean values across all threads in a warp:

```cuda
// src/kernels/warp_primitives.cu
__device__ bool vote_all_ptx(bool predicate) {
    int result;
    int pred = predicate ? 1 : 0;
    // Returns 1 if all threads in warp have predicate == true
    asm("vote.sync.all.pred %0, %1, 0xffffffff;"
        : "=r"(result)
        : "r"(pred)
    );
    return result != 0;
}

__device__ bool vote_any_ptx(bool predicate) {
    int result;
    int pred = predicate ? 1 : 0;
    // Returns 1 if any thread in warp has predicate == true
    asm("vote.sync.any.pred %0, %1, 0xffffffff;"
        : "=r"(result)
        : "r"(pred)
    );
    return result != 0;
}

__device__ unsigned int ballot_ptx(bool predicate) {
    unsigned int result;
    int pred = predicate ? 1 : 0;
    // Returns bitmask where bit i is set if thread i has predicate == true
    asm("vote.sync.ballot.b32 %0, %1, 0xffffffff;"
        : "=r"(result)
        : "r"(pred)
    );
    return result;
}
```

Source: `src/kernels/warp_primitives.cu:37-70`

### **41.6.3 Warp Reduction Example**

Using shuffle for efficient warp-level reduction:

```cuda
// src/kernels/warp_primitives.cu
__device__ int warp_reduce_sum_ptx(int val) {
    // Warp reduction using shuffle down
    #pragma unroll
    for (int offset = 16; offset > 0; offset /= 2) {
        val += shfl_down_ptx(val, offset);
    }
    return val;  // Valid in lane 0
}

__device__ int warp_reduce_max_ptx(int val) {
    // Warp reduction for maximum value
    #pragma unroll
    for (int offset = 16; offset > 0; offset /= 2) {
        int other = shfl_down_ptx(val, offset);
        val = max(val, other);
    }
    return val;  // Valid in lane 0
}
```

Source: `src/kernels/warp_primitives.cu:72-94`

---

## **41.7 PTX Generation and Analysis**

Understanding how to generate and analyze PTX code helps optimize CUDA kernels.

### **41.7.1 Generating PTX Code**

Generate PTX from CUDA source for inspection:

```bash
# Generate PTX for specific architecture
nvcc -ptx -arch=sm_80 kernel.cu -o kernel.ptx

# Generate PTX with optimization
nvcc -ptx -O3 -arch=sm_80 kernel.cu -o kernel.ptx

# Keep intermediate files (including PTX)
nvcc --keep -arch=sm_80 kernel.cu

# Generate PTX with line number information
nvcc -ptx -lineinfo -arch=sm_80 kernel.cu -o kernel.ptx
```

### **41.7.2 Analyzing Generated PTX**

```bash
# Disassemble CUDA binary to PTX
cuobjdump -ptx executable

# Disassemble to SASS (actual GPU assembly)
cuobjdump -sass executable

# Disassemble with line numbers
nvdisasm -c -fun kernel_name executable

# Analyze specific kernel
nvdisasm -fun my_kernel executable
```

### **41.7.3 PTX Optimization Directives**

```cuda
// Force specific optimization behavior
__global__ void __launch_bounds__(256, 2)
optimized_kernel(float* data, int n) {
    // __launch_bounds__(maxThreadsPerBlock, minBlocksPerMultiprocessor)
    // Hints to compiler for register allocation
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        data[idx] *= 2.0f;
    }
}
```

**Common Optimization Flags:**
- `--maxrregcount=N` - Limit register usage to N registers per thread
- `-use_fast_math` - Enable fast math approximations
- `-ftz=true` - Flush denormals to zero
- `-prec-div=false` - Use fast division
- `-prec-sqrt=false` - Use fast square root

---

## **41.8 Testing**

### **41.8.1 Unit Tests with GpuTest Base Class**

The `GpuTest` base class provides automatic CUDA device setup/teardown for test fixtures. Tests verify correctness of PTX operations against standard CUDA implementations.

```cuda
// test/unit/kernels/test_inline_ptx.cu
#include <gtest/gtest.h>
#include "gpu_gtest.h"
#include "kernels/inline_ptx.cu"

class InlinePTXTest : public GpuTest {
protected:
    void SetUp() override {
        GpuTest::SetUp();
    }
};

TEST_F(InlinePTXTest, AddOperation) {
    const int a = 42, b = 17;
    const int expected = 59;

    int result;
    cuda_malloc(&result, 1);

    // Launch kernel that uses add_ptx
    test_add_kernel<<<1, 1>>>(&result, a, b);
    CHECK_KERNEL_LAUNCH();

    int host_result;
    cuda_memcpy(&host_result, &result, 1, cudaMemcpyDeviceToHost);

    EXPECT_EQ(host_result, expected);
    cuda_free(result);
}

TEST_F(InlinePTXTest, PopulationCount) {
    unsigned int test_val = 0xF0F0F0F0;  // 16 bits set
    int expected = 16;

    // Test popc_ptx function
    int result;
    cuda_malloc(&result, 1);

    test_popc_kernel<<<1, 1>>>(&result, test_val);
    CHECK_KERNEL_LAUNCH();

    int host_result;
    cuda_memcpy(&host_result, &result, 1, cudaMemcpyDeviceToHost);

    EXPECT_EQ(host_result, expected);
    cuda_free(result);
}
```

Source: `test/unit/kernels/test_inline_ptx.cu:5-50`

### **41.8.2 Atomic Operations Tests**

```cuda
// test/unit/kernels/test_ptx_atomics.cu
TEST_F(PTXAtomicsTest, AtomicAddCorrectness) {
    const int num_threads = 1024;
    int* d_counter;
    cuda_malloc(&d_counter, 1);
    cuda_memset(d_counter, 0, 1);

    // Each thread atomically adds 1
    atomic_add_kernel<<<(num_threads+255)/256, 256>>>(d_counter, 1);
    CHECK_KERNEL_LAUNCH();

    int h_counter;
    cuda_memcpy(&h_counter, d_counter, 1, cudaMemcpyDeviceToHost);

    EXPECT_EQ(h_counter, num_threads);
    cuda_free(d_counter);
}

TEST_F(PTXAtomicsTest, AtomicCASLockFree) {
    const int limit = 100;
    const int num_increments = 1000;

    int* d_value;
    cuda_malloc(&d_value, 1);
    cuda_memset(d_value, 0, 1);

    // Test lock-free increment with CAS
    atomic_cas_inc_kernel<<<(num_increments+255)/256, 256>>>(d_value, limit);
    CHECK_KERNEL_LAUNCH();

    int h_value;
    cuda_memcpy(&h_value, d_value, 1, cudaMemcpyDeviceToHost);

    EXPECT_EQ(h_value, num_increments % limit);
    cuda_free(d_value);
}
```

Source: `test/unit/kernels/test_ptx_atomics.cu:8-45`

### **41.8.3 Warp Primitives Tests**

```cuda
// test/unit/kernels/test_warp_primitives.cu
TEST_F(WarpPrimitivesTest, ShuffleDownCorrectness) {
    const int warp_size = 32;
    int* d_input, *d_output;
    cuda_malloc(&d_input, warp_size);
    cuda_malloc(&d_output, warp_size);

    // Initialize with lane IDs
    init_lane_ids_kernel<<<1, warp_size>>>(d_input);

    // Test shuffle down by 1
    shuffle_down_kernel<<<1, warp_size>>>(d_output, d_input, 1);
    CHECK_KERNEL_LAUNCH();

    std::vector<int> h_output(warp_size);
    cuda_memcpy(h_output.data(), d_output, warp_size, cudaMemcpyDeviceToHost);

    // Verify: output[i] should be input[i+1] for i < 31
    for (int i = 0; i < warp_size - 1; i++) {
        EXPECT_EQ(h_output[i], i + 1);
    }

    cuda_free(d_input);
    cuda_free(d_output);
}

TEST_F(WarpPrimitivesTest, WarpReductionSum) {
    const int warp_size = 32;
    int* d_data, *d_result;
    cuda_malloc(&d_data, warp_size);
    cuda_malloc(&d_result, 1);

    // Initialize all to 1
    cuda_memset(d_data, 1, warp_size);

    // Reduce: sum should be 32
    warp_reduce_sum_kernel<<<1, warp_size>>>(d_result, d_data);
    CHECK_KERNEL_LAUNCH();

    int h_result;
    cuda_memcpy(&h_result, d_result, 1, cudaMemcpyDeviceToHost);

    EXPECT_EQ(h_result, warp_size);

    cuda_free(d_data);
    cuda_free(d_result);
}
```

Source: `test/unit/kernels/test_warp_primitives.cu:10-60`

---

## **41.9 Summary**

### **Key Takeaways**
1. **PTX Overview**: PTX provides low-level GPU control while maintaining forward compatibility across architectures
2. **Inline PTX**: Embed PTX instructions in CUDA C++ for fine-grained optimization of critical code sections
3. **Memory Control**: Use PTX cache hints and volatile operations for optimized memory access patterns
4. **Atomic Operations**: PTX atomics offer explicit control over memory ordering and synchronization
5. **Warp Primitives**: Shuffle and vote operations enable efficient thread communication within warps
6. **Analysis Tools**: Generate and analyze PTX code to understand and optimize kernel behavior

### **Performance Benefits**
- **Reduced Overhead**: Direct instruction selection eliminates compiler interpretation
- **Explicit Caching**: Cache modifiers optimize memory hierarchy utilization
- **Warp Efficiency**: Shuffle operations avoid shared memory bank conflicts
- **Lock-Free Algorithms**: CAS enables efficient lock-free data structures

### **Common Use Cases**
| Use Case | PTX Feature | Benefit |
|----------|-------------|---------|
| Critical inner loops | Inline arithmetic | Direct instruction control |
| Memory streaming | Cache modifiers | Optimized bandwidth |
| Thread communication | Shuffle operations | No shared memory overhead |
| Synchronization | Atomic CAS | Lock-free algorithms |
| Bit manipulation | Bit intrinsics | Single-instruction operations |

### **When to Use PTX**
✅ **Good for:**
- Performance-critical inner loops
- Accessing hardware features not in CUDA C++
- Custom memory access patterns
- Warp-level algorithms
- Explicit instruction selection

❌ **Avoid for:**
- General application code (use CUDA C++)
- Cross-platform code (PTX is NVIDIA-specific)
- Rapid prototyping (less readable)
- Simple operations (compiler does well)

### **Next Steps**
- 📚 Continue to [Part 42: Compiler Optimizations](../42.Compiler_Optimizations/README.md) to understand NVCC optimization strategies
- 🔧 Experiment with PTX in performance-critical sections of your kernels
- 📊 Profile PTX-optimized code with Nsight Compute to measure improvements
- 🧪 Compare PTX implementations against CUDA C++ equivalents

### **References**
- [PTX ISA Documentation](https://docs.nvidia.com/cuda/parallel-thread-execution/)
- [CUDA Inline PTX Assembly](https://docs.nvidia.com/cuda/inline-ptx-assembly/)
- [CUDA Programming Guide - PTX](https://docs.nvidia.com/cuda/cuda-c-programming-guide/index.html#ptx)
- [Warp-Level Primitives](https://developer.nvidia.com/blog/using-cuda-warp-level-primitives/)

---
