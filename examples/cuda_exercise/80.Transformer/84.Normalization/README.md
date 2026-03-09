# Part 84: Normalization
**Goal**: Implement RMSNorm using warp/block reduction building blocks from Module 88, supporting both fp32 and fp16 precision for transformer pre-normalization layers.

## Project Structure
```
84.Normalization/
├── CMakeLists.txt
├── README.md
├── doxygen/
│   ├── Doxyfile.in
│   └── mainpage.md
├── src/
│   ├── CMakeLists.txt
│   ├── common/
│   │   └── rmsnorm.cuh           # RMSNorm launch function declarations
│   └── kernels/
│       └── rmsnorm.cu            # RMSNorm kernel using Module 88 primitives
└── test/
    ├── CMakeLists.txt
    └── unit/
        └── kernels/
            └── test_rmsnorm.cu
```

## Quick Navigation
- [84.1 RMSNorm](#841-rmsnorm)
- [84.2 Build & Run](#842-build--run)
- [84.3 Summary](#843-summary)

---

## **84.1 RMSNorm**
Root Mean Square Layer Normalization simplifies LayerNorm by dropping the mean subtraction step, computing only the root mean square for scaling. This reduces per-row computation from two reductions to one, while empirically maintaining similar model quality in architectures such as LLaMA.

### **84.1.1 Algorithm**
RMSNorm computes: `output[i] = weight[i] * input[i] * rsqrt(mean(input^2) + eps)`

The kernel assigns one thread block per row. Phase 1 computes the sum of squares via a strided accumulation loop followed by `block_reduce_sum` (from Module 88). Phase 2 applies the element-wise normalization.

```cpp
// rmsnorm.cu - RMSNorm kernel
__global__ void rmsnorm_kernel(float* output, const float* input,
                                const float* weight, int hidden_dim, float eps) {
    extern __shared__ float smem[];
    int row = blockIdx.x;
    const float* row_input = input + row * hidden_dim;
    float* row_output = output + row * hidden_dim;

    float rms_scale = compute_rms_rsqrt(row_input, hidden_dim, eps, smem);

    for (int i = threadIdx.x; i < hidden_dim; i += blockDim.x) {
        row_output[i] = weight[i] * row_input[i] * rms_scale;
    }
}
```

**Key Points**:
- One block per row ensures each row is normalized independently
- `compute_rms_rsqrt` handles the strided accumulation + block reduction internally
- `rsqrtf` is a single hardware instruction on NVIDIA GPUs
- Block size is adaptive: 256 for hidden_dim >= 256, otherwise rounded to warp boundary

**Source**: `src/kernels/rmsnorm.cu`

### **84.1.2 fp16 Variant**
The fp16 kernel loads `half` values, converts to `float` for the reduction to maintain numerical stability, and converts back to `half` at the store.

**Key Points**:
- All intermediate reductions are done in fp32
- Shared memory buffer stores fp32 partial sums
- Final result is converted back to fp16 only at the store step

**Source**: `src/kernels/rmsnorm.cu`

---

## **84.2 Build & Run**
Build and test from the repository build directory.

```bash
cmake --build . --target 84_Normalization_test
ctest -R 84_Normalization

# Generate documentation
ninja doxygen_84_Normalization
```

---

## **84.3 Summary**

- **Key Takeaways**:
  - RMSNorm uses one reduction per row (vs two for LayerNorm), making it faster
  - The kernel reuses `compute_rms_rsqrt` from Module 88, demonstrating the common API layer's composability
  - fp16 variant uses fp32 internal accumulation for numerical stability

- **Common Errors**:

  | Error | Cause | Solution |
  |---|---|---|
  | NaN output | Input contains NaN or eps=0 | Validate inputs; use eps >= 1e-8 |
  | fp16 precision loss | Accumulating sum_sq in fp16 | Internal computation is always fp32 |

- **Next Steps**: [85.Tensor_Operations](../85.Tensor_Operations/README.md) -- transpose and bias_residual utilities used alongside RMSNorm in transformer blocks

- **References**:
  - [RMSNorm paper (Zhang & Sennrich, 2019)](https://arxiv.org/abs/1910.07467)
  - [88.Normalization_Common_API](../88.Normalization_Common_API/README.md) -- reduction primitives
