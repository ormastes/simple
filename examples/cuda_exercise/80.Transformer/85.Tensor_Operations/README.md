# Part 85: Tensor Operations
**Goal**: Implement fused bias-residual addition and shared-memory-optimized matrix transpose kernels for transformer inference workloads.

## Project Structure
```
85.Tensor_Operations/
├── CMakeLists.txt
├── README.md
├── doxygen/
│   ├── Doxyfile.in
│   └── mainpage.md
├── src/
│   ├── CMakeLists.txt
│   ├── common/
│   │   ├── bias_residual.cuh        # Bias + residual launch declarations
│   │   └── transpose_permute.cuh    # Transpose launch declarations
│   └── kernels/
│       ├── bias_residual.cu         # Fused bias + residual kernel
│       └── transpose_permute.cu     # Shared-memory transpose kernel
└── test/
    ├── CMakeLists.txt
    └── unit/
        └── kernels/
            ├── test_bias_residual.cu
            └── test_transpose.cu
```

## Quick Navigation
- [85.1 Bias + Residual Fusion](#851-bias--residual-fusion)
- [85.2 Transpose](#852-transpose)
- [85.3 Summary](#853-summary)
- [Build & Run](#build--run)

---

## **85.1 Bias + Residual Fusion**
In transformer blocks, the output of every linear projection is followed by a bias addition and a residual connection. Fusing these two element-wise operations into a single kernel halves the global memory traffic compared to running them separately.

### **85.1.1 Algorithm**
The kernel computes `output[row][col] = input[row][col] + bias[col] + residual[row][col]` using a flat 1D grid. Each thread handles one element, reading the bias from a per-column vector that is broadcast along the row dimension.

```cpp
// bias_residual.cu - Fused bias + residual kernel
__global__ void bias_residual_kernel(float* output, const float* input,
                                      const float* bias, const float* residual,
                                      int rows, int cols) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= rows * cols) return;
    int col = idx % cols;
    output[idx] = input[idx] + bias[col] + residual[idx];
}
```

**Key Points**:
- Simple 1D thread mapping covers all elements
- Bias is indexed by `col = idx % cols`, broadcasting along rows
- Bandwidth-bound: 3 reads + 1 write per element
- Uses 256 threads per block for good occupancy

**Source**: `src/kernels/bias_residual.cu`

---

## **85.2 Transpose**
Matrix transpose is needed for attention head reshaping and layout conversions between row-major and column-major formats. A naive transpose suffers from non-coalesced global memory accesses; the shared-memory tiled approach solves this.

### **85.2.1 Shared Memory Tiling**
The kernel uses 32x32 tiles loaded cooperatively into shared memory. The +1 column padding (`TILE_DIM + 1`) eliminates shared memory bank conflicts during the transposed read phase. Each thread block uses `BLOCK_ROWS = 8`, meaning each thread processes 4 elements per tile.

```cpp
// transpose_permute.cu - Shared memory transpose
__global__ void transpose_kernel(float* output, const float* input, int rows, int cols) {
    __shared__ float tile[TILE_DIM][TILE_DIM + 1];  // +1 avoids bank conflicts

    // Load tile from input (coalesced reads)
    // ...
    __syncthreads();
    // Store transposed tile to output (coalesced writes)
    // ...
}
```

**Key Points**:
- Coalesced global reads and writes in both load and store phases
- `TILE_DIM + 1` padding prevents 32-way bank conflicts
- Handles non-tile-aligned dimensions via bounds checking
- Grid dimensions: `ceil(cols/32) x ceil(rows/32)`

**Source**: `src/kernels/transpose_permute.cu`

---

## **85.3 Summary**

- **Key Takeaways**:
  - Fusing bias + residual into one kernel halves memory traffic vs separate passes
  - Shared-memory transpose with +1 padding achieves near-peak memory bandwidth
  - Both kernels handle non-aligned dimensions correctly via bounds checking

- **Common Errors**:

  | Error | Cause | Solution |
  |---|---|---|
  | Wrong bias values per row | Incorrect column index calculation | Use `idx % cols` for the bias index |
  | Bank conflicts in transpose | Missing +1 padding in shared memory | Declare `tile[DIM][DIM + 1]` |
  | Out-of-bounds access | Matrix dimensions not multiple of tile size | Add bounds checks in kernel |

- **Next Steps**: [84.Normalization](../84.Normalization/README.md) -- RMSNorm that composes with bias_residual in full transformer blocks

- **References**:
  - [CUDA C Programming Guide: Shared Memory](https://docs.nvidia.com/cuda/cuda-c-programming-guide/index.html#shared-memory)
  - [89.Tensor_Ops_Common_API](../89.Tensor_Ops_Common_API/README.md) -- common tensor utilities

---

## Build & Run

```bash
# From the repository build directory
cmake --build . --target 85_Tensor_Operations_test
ctest -R 85_Tensor_Operations

# Generate documentation
ninja doxygen_85_Tensor_Operations
```
