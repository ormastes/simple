# Part 83: MLP
**Goal**: Implement standalone GPU activation function kernels (GELU, SiLU, SwiGLU) for transformer feed-forward network layers, supporting both fp32 and fp16 precision.

## Project Structure
```
83.MLP/
├── CMakeLists.txt
├── README.md
├── doxygen/
│   ├── Doxyfile.in
│   └── mainpage.md
├── src/
│   ├── CMakeLists.txt
│   ├── common/
│   │   └── activation.cuh       # Launch function declarations
│   └── kernels/
│       └── activation.cu        # GELU, SiLU, SwiGLU kernel implementations
└── test/
    ├── CMakeLists.txt
    └── unit/
        └── kernels/
            └── test_activation.cu
```

## Quick Navigation
- [83.1 GELU Activation](#831-gelu-activation)
- [83.2 SiLU / Swish Activation](#832-silu--swish-activation)
- [83.3 Fused Gate Projections (SwiGLU)](#833-fused-gate-projections-swiglu)
- [83.4 Summary](#834-summary)
- [Build & Run](#build--run)

---

## **83.1 GELU Activation**
The Gaussian Error Linear Unit is the default activation in GPT-2/3 and BERT-style transformers. It provides a smooth approximation to ReLU that allows small negative gradients, improving training stability.

### **83.1.1 Tanh Approximation**
The fast tanh approximation avoids the need for `erff()` while maintaining high accuracy.

```cpp
// activation.cu - GELU kernel
__global__ void gelu_kernel(float* output, const float* input, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        float x = input[idx];
        float cdf = 0.5f * (1.0f + tanhf(0.7978845608f * (x + 0.044715f * x * x * x)));
        output[idx] = x * cdf;
    }
}
```

**Key Points**:
- Constant `0.7978845608 = sqrt(2/pi)` is precomputed
- The cubic term `0.044715 * x^3` improves the tanh-based CDF approximation
- GELU(0) = 0, GELU(x) approaches x for large positive x, approaches 0 for large negative x
- fp16 variant does internal computation in fp32 for accuracy

**Source**: `src/kernels/activation.cu`

### **83.1.2 fp16 Variant**
The fp16 GELU converts to fp32 for the computation and converts back, avoiding precision loss in the cubic and tanh operations.

```cpp
// activation.cu - fp16 GELU
__global__ void gelu_fp16_kernel(half* output, const half* input, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        float x = __half2float(input[idx]);
        float cdf = 0.5f * (1.0f + tanhf(0.7978845608f * (x + 0.044715f * x * x * x)));
        output[idx] = __float2half(x * cdf);
    }
}
```

---

## **83.2 SiLU / Swish Activation**
SiLU (Sigmoid Linear Unit), also known as Swish, is used in modern architectures like LLaMA as the base activation for SwiGLU gating. It is smooth, non-monotonic, and self-gated.

### **83.2.1 Implementation**
SiLU is defined as `SiLU(x) = x * sigmoid(x) = x / (1 + exp(-x))`.

```cpp
// activation.cu - SiLU kernel
__global__ void silu_kernel(float* output, const float* input, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) {
        float x = input[idx];
        output[idx] = x / (1.0f + expf(-x));
    }
}
```

**Key Points**:
- SiLU(0) = 0, SiLU(x) approaches x for large positive x
- Has a small negative region (minimum near x = -1.28)
- Single `expf` instruction per element

**Source**: `src/kernels/activation.cu`

---

## **83.3 Fused Gate Projections (SwiGLU)**
SwiGLU is the gated activation used in LLaMA and PaLM FFN blocks. It splits the FFN intermediate representation into two halves: one passes through SiLU, the other acts as a gate.

### **83.3.1 SwiGLU Kernel**
The input tensor of size `n` is split at the midpoint: elements `[0, n/2)` are the value path (passed through SiLU), elements `[n/2, n)` are the gate that multiplies the activated values.

```cpp
// activation.cu - SwiGLU kernel
__global__ void swiglu_kernel(float* output, const float* input, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    int half_n = n / 2;
    if (idx < half_n) {
        float x = input[idx];
        float gate = input[idx + half_n];
        float silu_x = x / (1.0f + expf(-x));
        output[idx] = gate * silu_x;
    }
}
```

**Key Points**:
- Output size is `n/2` (gating halves the dimension)
- When gate is zero, output is zero regardless of x
- In a full LLaMA FFN: `output = down_proj(SwiGLU(gate_proj(x), up_proj(x)))`
- The split layout matches the output of two parallel linear projections concatenated

**Source**: `src/kernels/activation.cu`

---

## **83.4 Summary**

- **Key Takeaways**:
  - GELU (tanh approximation) is the standard GPT-2/3/BERT activation
  - SiLU is the smooth self-gated activation used as the base for SwiGLU
  - SwiGLU splits the input and applies gated SiLU, halving the output dimension
  - fp16 variants compute internally in fp32 to maintain precision
  - These standalone kernels complement the fused GELU in Module 81's epilogue fusion

- **Performance Characteristics**:
  - All kernels are bandwidth-bound (one read + one write per element)
  - 256 threads per block provides good occupancy across architectures
  - SwiGLU reads `n` elements but writes only `n/2`

- **Common Errors**:

  | Error | Cause | Solution |
  |---|---|---|
  | SwiGLU output size wrong | Allocating n elements instead of n/2 | Output buffer must be half the input size |
  | fp16 precision loss | Using fp16 arithmetic for tanh/exp | Use fp32 internally, convert only at load/store |
  | NaN in GELU for large inputs | Overflow in cubic term | Input range should be within [-10, 10] for fp16 |

- **Next Steps**: [82.Attention_Kernels](../82.Attention_Kernels/README.md) -- uses these activation functions in attention output projections

- **References**:
  - [GELU paper](https://arxiv.org/abs/1606.08415)
  - [SwiGLU paper](https://arxiv.org/abs/2002.05202)
  - [81.Core_GEMM_Operations](../81.Core_GEMM_Operations/README.md) -- fused GELU in GEMM epilogue

---

## Build & Run

```bash
# From the repository build directory
cmake --build . --target 83_MLP_test
ctest -R 83_MLP

# Generate documentation
ninja doxygen_83_MLP
```
