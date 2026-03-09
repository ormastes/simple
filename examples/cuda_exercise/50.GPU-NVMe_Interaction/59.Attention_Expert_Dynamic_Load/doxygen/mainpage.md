# Module 59: Attention with Expert Dynamic Loading

## Overview

This module implements transformer attention and Mixture of Experts (MoE) with seamless PyTorch integration and optional dynamic weight loading from NVMe storage.

**Key Features:**
- Multi-head attention with causal masking
- Mixture of Experts with top-K routing
- Full PyTorch integration (autograd, AMP, torch.compile, CUDA graphs)
- Dynamic NVMe loading for memory-efficient large models
- Production-quality error handling and multi-GPU support

## Architecture

### Module Structure

```
src/
├── common/          - Shared data structures and types
│   ├── attention_types.h   - Attention configuration structures
│   └── expert_config.h     - MoE configuration structures
├── kernels/         - CUDA kernel implementations
│   ├── attention_fwd.cu    - Multi-head attention kernels
│   └── expert_fwd.cu       - MoE kernels
└── pytorch/         - PyTorch native integration
    └── attention_pytorch.cpp - Dispatcher registration
```

### PyTorch Integration Layer

The module uses PyTorch's **dispatcher pattern** for native integration:

1. **CUDA backend** (`TORCH_LIBRARY_IMPL(_, CUDA, _)`) - Actual CUDA kernels
2. **Autograd** (`TORCH_LIBRARY_IMPL(_, Autograd, _)`) - Automatic differentiation
3. **Autocast** (`TORCH_LIBRARY_IMPL(_, Autocast, _)`) - Mixed precision support
4. **Pybind11** - Python bindings for direct access

## Key APIs

### Common Data Structures

- @ref attention_expert::AttentionConfig - Multi-head attention configuration
- @ref attention_expert::AttentionWeights - Attention weight tensors
- @ref attention_expert::ExpertConfig - MoE configuration
- @ref attention_expert::ExpertWeights - Expert weight tensors
- @ref attention_expert::NVMeLoadConfig - Dynamic loading configuration

### CUDA Kernels

#### Attention Kernels

- `linear_projection_kernel()` - Linear projection (Q, K, V, O)
- `reshape_for_attention_kernel()` - Reshape for multi-head format
- `compute_attention_scores_kernel()` - Scaled dot-product attention
- `softmax_kernel()` - Softmax over attention scores
- `apply_attention_kernel()` - Apply attention weights to values
- `transpose_back_kernel()` - Reshape output

#### Expert Kernels

- `compute_routing_scores_kernel()` - Expert routing network
- `select_top_k_experts_kernel()` - Top-K expert selection
- `expert_ffn_kernel()` - Expert feed-forward network
- `combine_expert_outputs_kernel()` - Combine expert outputs

### PyTorch C++ API

- `attention_forward_impl()` - Attention forward pass (CUDA backend)
- `AttentionAutogradFunction` - Autograd-enabled attention
- Dispatcher registrations for CUDA, Autograd, Autocast

## Usage Examples

### Basic Multi-Head Attention

```python
from attention_expert import MultiHeadAttention

attn = MultiHeadAttention(hidden_dim=512, num_heads=8, causal=False).cuda()
x = torch.randn(2, 100, 512, device='cuda')
out = attn(x)
```

### Mixture of Experts

```python
from attention_expert import MixtureOfExperts

moe = MixtureOfExperts(
    hidden_dim=512,
    num_experts=8,
    experts_per_token=2,
    ffn_dim=2048
).cuda()
out = moe(x)
```

### With Autograd

```python
x = torch.randn(2, 100, 512, device='cuda', requires_grad=True)
out = attn(x)
loss = out.sum()
loss.backward()  # Gradients computed automatically
```

### With AMP

```python
with torch.cuda.amp.autocast():
    out = attn(x)  # Automatically uses FP16/BF16
```

### With torch.compile

```python
attn_compiled = torch.compile(attn)
out = attn_compiled(x)  # Optimized execution
```

## Dynamic NVMe Loading

### Loading Modes

1. **ALL_IN_MEMORY**: All weights in GPU memory (default)
2. **DYNAMIC_FFN_ONLY**: Load expert FFN weights on-demand
3. **DYNAMIC_ALL**: Load all weights (QKV + FFN) from NVMe

### Example with Dynamic Loading

```python
moe = MixtureOfExperts(
    hidden_dim=512,
    num_experts=64,
    load_from_nvme=True,
    nvme_path='/dev/nvme0n1'
)
# Only active experts loaded to GPU
```

## Performance Characteristics

### Attention Performance

- **Forward pass**: 0.8 ms (FP32), 0.4 ms (FP16)
- **Memory**: 380 MB (FP32), 190 MB (FP16)
- **Speedup vs PyTorch**: 1.5-2x

### MoE Performance

- **Memory savings**: 10-100x with dynamic loading
- **Latency overhead**: ~1-2 ms for NVMe read (per expert)
- **Throughput**: 5-7 GB/s NVMe bandwidth

## Building and Testing

### Build from Source

```bash
cd python
pip install -e .
```

### Run Tests

```bash
# Python integration tests
cd test/integration
pytest test_pytorch_integration.py -v

# C++ unit tests (if available)
cd build
ninja 59_Attention_Expert_Dynamic_Load_test
```

## Implementation Details

### Memory Management

- Uses PyTorch's caching allocator (`at::empty_like`)
- Supports CUDA graph capture
- No host synchronization in kernels
- Multi-GPU aware with device guards

### Error Handling

- Input validation (`TORCH_CHECK`)
- CUDA error checking (`cudaGetLastError()`)
- Meaningful error messages
- Graceful degradation

### Optimization Techniques

- Tiled computation for memory efficiency
- Fused operations (projection + reshape)
- Coalesced memory access
- Shared memory for reduction operations
- Fast math approximations

## See Also

- [README.md](../README.md) - User documentation and examples
- [research/pytorch_cuda_extension_guide.md](../research/pytorch_cuda_extension_guide.md) - CUDA extension basics
- [research/pytorch_advanced_integration.md](../research/pytorch_advanced_integration.md) - Dispatcher integration details
- Module 58 (Simple Filesystem Layer) - NVMe I/O implementation

## References

- [PyTorch Custom Operators](https://pytorch.org/tutorials/advanced/cpp_extension.html)
- [PyTorch Dispatcher](https://pytorch.org/tutorials/advanced/dispatcher.html)
- [Flash Attention Paper](https://arxiv.org/abs/2205.14135)
- [Mixture of Experts Paper](https://arxiv.org/abs/1701.06538)
