# 🎯 Part 89: Tensor Ops Common API

**Goal**: Provide vectorized I/O and memory layout utilities that serve as the foundation for all transformer CUDA kernels, maximizing memory bandwidth and ensuring correct data layouts for Tensor Core operations.

## Project Structure

```
89.Tensor_Ops_Common_API/
├── README.md
├── CMakeLists.txt
├── doxygen/
│   ├── Doxyfile.in
│   └── mainpage.md
├── src/
│   └── common/
│       ├── vector_io.cuh          # Vectorized load/store templates
│       ├── vector_io.cu           # Compilation unit
│       ├── layout_swizzle.cuh     # Layout indexing and swizzle
│       └── layout_swizzle.cu      # Compilation unit
└── test/
    └── unit/
        └── kernels/
            ├── test_vector_io.cu
            └── test_layout_swizzle.cu
```

## Quick Navigation

- [89.1 Vectorized I/O](#891-vectorized-io)
- [89.2 Layout Swizzle](#892-layout-swizzle)
- [89.3 Summary](#893-summary)
- [Build & Run](#build--run)

---

## **89.1 Vectorized I/O**

GPU memory bandwidth is the primary bottleneck in transformer inference. Vectorized loads and stores issue fewer memory transactions by packing multiple elements into a single wide transaction.

### **89.1.1 Float4 and Float2 Access**

The core vectorized operations use CUDA vector types to perform 128-bit (float4) and 64-bit (float2) memory accesses in a single instruction.

```cpp
// common/vector_io.cuh - Vectorized load/store
namespace transformer {

__device__ __forceinline__ float4 load_float4(const float* addr) {
    return *reinterpret_cast<const float4*>(addr);
}

__device__ __forceinline__ void store_float4(float* addr, float4 val) {
    *reinterpret_cast<float4*>(addr) = val;
}

} // namespace transformer
```

**Key Points**:
- float4 loads require 16-byte aligned addresses
- float2 loads require 8-byte aligned addresses
- `cudaMalloc` guarantees 256-byte alignment, so base pointers are always safe
- Offsets within arrays may break alignment (e.g., `ptr + 1` is not 16-byte aligned)

**Source**: `src/common/vector_io.cuh`

### **89.1.2 Half-Precision Support**

Half2 vectorized operations enable efficient fp16 memory access, critical for Tensor Core workflows where inputs are stored in half precision.

```cpp
// common/vector_io.cuh - Half-precision vectorized access
__device__ __forceinline__ half2 load_half2(const half* addr) {
    return *reinterpret_cast<const half2*>(addr);
}
```

**Key Points**:
- half2 loads/stores are 32-bit (4-byte) aligned operations
- Commonly used for loading WMMA fragment inputs
- Enables 2x throughput compared to scalar half loads

### **89.1.3 Alignment Checking and Safe Loads**

Not all memory accesses can guarantee alignment. The `is_aligned<N>` template and `safe_load_float4` provide runtime checking with automatic fallback.

```cpp
// common/vector_io.cuh - Safe load with fallback
__device__ __forceinline__ void safe_load_float4(float* dst, const float* src) {
    if (is_aligned<16>(src)) {
        float4 v = load_float4(src);
        dst[0] = v.x; dst[1] = v.y; dst[2] = v.z; dst[3] = v.w;
    } else {
        dst[0] = src[0]; dst[1] = src[1]; dst[2] = src[2]; dst[3] = src[3];
    }
}
```

**Key Points**:
- Use safe loads when pointer alignment cannot be statically guaranteed
- The branch is well-predicted since alignment is typically consistent across warps
- `vectorized_copy<VEC_SIZE>` automatically handles the aligned fast path and scalar remainder

### **89.1.4 Practical Usage**

```cpp
// Loading a tile from global memory into shared memory
__global__ void load_tile_kernel(const float* input, float* smem_tile,
                                  int stride, int tile_size) {
    int tid = threadIdx.x;
    // Each thread loads 4 elements using vectorized access
    if (tid * 4 < tile_size) {
        float4 v = transformer::load_float4(input + tid * 4);
        smem_tile[tid * 4 + 0] = v.x;
        smem_tile[tid * 4 + 1] = v.y;
        smem_tile[tid * 4 + 2] = v.z;
        smem_tile[tid * 4 + 3] = v.w;
    }
}
```

---

## **89.2 Layout Swizzle**

Tensor layout determines how multi-dimensional data maps to linear GPU memory. Correct layout selection is critical for coalesced access patterns and Tensor Core compatibility.

### **89.2.1 Row-Major and Column-Major Indexing**

Standard layout functions convert 2D coordinates to linear memory offsets. Row-major is the default C/CUDA layout; column-major is used for transposed matrices and certain BLAS conventions.

```cpp
// common/layout_swizzle.cuh - Standard layout indexing
__host__ __device__ __forceinline__
int row_major_idx(int row, int col, int num_cols) {
    return row * num_cols + col;
}

__host__ __device__ __forceinline__
int col_major_idx(int row, int col, int num_rows) {
    return col * num_rows + row;
}
```

**Key Points**:
- Row-major: consecutive columns are contiguous in memory (coalesced row access)
- Column-major: consecutive rows are contiguous in memory (coalesced column access)
- These functions are `__host__ __device__` for use in both CPU setup and GPU kernels

### **89.2.2 Col32 Layout for Tensor Cores**

Tensor Core WMMA operations require specific data layouts. Col32 groups columns into blocks of 32, with rows interleaved within each block, matching WMMA fragment load patterns.

```cpp
// common/layout_swizzle.cuh - Col32 layout
__host__ __device__ __forceinline__
int col32_idx(int row, int col, int num_rows) {
    int col_block = col / 32;
    int col_within = col % 32;
    return col_block * (num_rows * 32) + row * 32 + col_within;
}
```

**Key Points**:
- `col32_padded(dim)` rounds dimensions up to multiples of 32
- Col32 eliminates bank conflicts when loading WMMA fragments from shared memory
- Required for INT8 Tensor Core operations (e.g., DP4A GEMM)

### **89.2.3 3D Stride Helper**

The `StrideHelper` struct encapsulates stride computation for batched 3D tensors, commonly used for `[Batch, Rows, Cols]` or `[Batch, Heads, SeqLen]` dimensions.

```cpp
// common/layout_swizzle.cuh - 3D tensor indexing
transformer::StrideHelper sh = transformer::make_row_major_3d(M, N);
int offset = sh(batch, row, col);  // batch * M*N + row * N + col
```

**Key Points**:
- Avoids repetitive stride arithmetic in kernel code
- Strides are stored as struct members for efficient device-side access
- `make_row_major_3d(M, N)` creates strides `{M*N, N, 1}`

### **89.2.4 Shared Memory Swizzle**

Bank conflicts occur when multiple threads in a warp access the same shared memory bank simultaneously. The XOR-based swizzle function remaps indices to spread accesses across banks.

```cpp
// common/layout_swizzle.cuh - Bank conflict avoidance
__device__ __forceinline__
int smem_swizzle(int idx) {
    return idx ^ ((idx >> 4) & 0x7);
}
```

**Key Points**:
- Zero overhead: single XOR and shift instruction
- Effective for tile sizes that are multiples of 32 (typical for GEMM tiles)
- Indices below 16 are identity-mapped (swizzle activates for larger offsets)

---

## **89.3 Summary**

- **Key Takeaways**:
  - Vectorized loads (float4/float2/half2) maximize memory bandwidth by issuing fewer, wider transactions
  - Alignment checking with `is_aligned<N>` prevents undefined behavior from misaligned vector access
  - Col32 layout is essential for Tensor Core compatibility and bank-conflict-free shared memory access
  - The StrideHelper abstraction simplifies batched tensor indexing throughout transformer kernels
  - XOR-based swizzle is a zero-cost technique for reducing shared memory bank conflicts

- **Performance Characteristics**:
  - float4 loads: up to 4x bandwidth improvement over scalar loads on aligned data
  - Col32 layout: eliminates shared memory bank conflicts for 32-wide warp access patterns
  - smem_swizzle: 1 ALU instruction overhead per index computation

- **Common Errors**:

  | Error | Cause | Solution |
  |-------|-------|----------|
  | `misaligned address` fault | Casting unaligned pointer to float4* | Use `safe_load_float4` or check with `is_aligned<16>` |
  | Wrong matrix values after Col32 | Forgetting to pad dimensions to multiples of 32 | Use `col32_padded()` for allocation size |
  | Bank conflicts in shared memory | Sequential index pattern across warp threads | Apply `smem_swizzle()` to shared memory indices |

- **Next Steps**: These utilities are consumed by [86.Core_Common_API](../86.Core_Common_API/README.md) for GEMM tile loading and [82.Attention_Kernels](../82.Attention_Kernels/README.md) for QKV tensor access patterns.

- **References**:
  - [CUDA C++ Programming Guide: Memory Access Patterns](https://docs.nvidia.com/cuda/cuda-c-programming-guide/)
  - [CUDA WMMA API](https://docs.nvidia.com/cuda/cuda-c-programming-guide/index.html#wmma)
  - [Shared Memory Bank Conflicts](https://developer.nvidia.com/blog/using-shared-memory-cuda-cc/)

---

## Build & Run

```bash
# From the build directory
cmake --build . --target 89_Tensor_Ops_Common_API_test
ctest -R 89_Tensor_Ops_Common_API

# Generate documentation
ninja doxygen_89_Tensor_Ops_Common_API
```

---
