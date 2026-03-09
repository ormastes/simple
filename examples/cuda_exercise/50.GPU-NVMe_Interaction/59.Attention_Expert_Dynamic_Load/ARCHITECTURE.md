# 🏗️ Architecture Documentation
## Module 59: Attention with Expert Dynamic Loading

This document provides detailed architectural views of the PyTorch-native CUDA extension with NVMe dynamic loading support.

---

## Table of Contents

- [1. System Overview](#1-system-overview)
- [2. Layer Architecture](#2-layer-architecture)
- [3. Attention Pipeline](#3-attention-pipeline)
- [4. Mixture of Experts Flow](#4-mixture-of-experts-flow)
- [5. PyTorch Dispatcher Integration](#5-pytorch-dispatcher-integration)
- [6. NVMe Tensor Loader](#6-nvme-tensor-loader)
- [7. Data Structures](#7-data-structures)
- [8. File Organization](#8-file-organization)

---

## 1. System Overview

The system consists of four main layers providing seamless integration between Python, PyTorch, CUDA kernels, and NVMe storage.

```mermaid
graph TB
    subgraph "Python Layer"
        A[Python API<br/>ops.py]
        B[MultiHeadAttention<br/>nn.Module]
        C[MixtureOfExperts<br/>nn.Module]
    end

    subgraph "PyTorch Integration Layer"
        D[PyTorch Dispatcher<br/>attention_pytorch.cpp]
        E[Autograd Function]
        F[Autocast Handler<br/>AMP Support]
        G[NVMe Tensor Loader<br/>nvme_tensor_loader.cpp]
    end

    subgraph "CUDA Kernel Layer"
        H[Attention Kernels<br/>attention_fwd.cu]
        I[Expert Kernels<br/>expert_fwd.cu]
        J[Linear Projection]
        K[Attention Scores]
        L[Softmax]
        M[Expert Routing]
        N[Expert FFN]
    end

    subgraph "Storage Layer"
        O[GPU Memory<br/>Weight Cache]
        P[NVMe Storage<br/>Dynamic Weights]
        Q[Pinned Host Memory<br/>I/O Buffer]
    end

    A --> B
    A --> C
    B --> D
    C --> D
    D --> E
    D --> F
    D --> G
    E --> H
    E --> I
    F --> H
    F --> I
    G --> P
    G --> Q
    H --> J
    H --> K
    H --> L
    I --> M
    I --> N
    J --> O
    K --> O
    L --> O
    M --> O
    N --> O
    N --> P

    style A fill:#e1f5ff
    style D fill:#fff4e1
    style H fill:#ffe1e1
    style P fill:#e1ffe1
```

**Key Design Principles:**

1. **Native PyTorch Integration**: Uses dispatcher pattern (not just pybind11) for full autograd/AMP/compile support
2. **Layered Abstraction**: Clear separation between Python API, PyTorch integration, CUDA kernels, and storage
3. **Dynamic Loading**: Optional NVMe loading enables models larger than GPU memory
4. **Performance**: Fused CUDA kernels minimize memory bandwidth

---

## 2. Layer Architecture

Detailed view of how components interact across layers.

```mermaid
graph LR
    subgraph "Layer 1: Python API"
        A1[MultiHeadAttention]
        A2[MixtureOfExperts]
        A3[Training Loop]
    end

    subgraph "Layer 2: PyTorch Dispatcher"
        B1[TORCH_LIBRARY<br/>Schema Registration]
        B2[CUDA Backend<br/>attention_forward_impl]
        B3[Autograd Backend<br/>AttentionAutogradFunction]
        B4[Autocast Backend<br/>FP16/BF16 Casting]
    end

    subgraph "Layer 3: CUDA Kernels"
        C1[linear_projection_kernel]
        C2[compute_attention_scores_kernel]
        C3[softmax_kernel]
        C4[compute_routing_scores_kernel]
        C5[expert_ffn_kernel]
    end

    subgraph "Layer 4: Storage Backend"
        D1[cudaMalloc<br/>Temporary Buffers]
        D2[NVMe I/O<br/>O_DIRECT reads]
        D3[Pinned Memory<br/>Staging Buffer]
    end

    A1 --> B1
    A2 --> B1
    A3 --> A1
    A3 --> A2

    B1 --> B2
    B1 --> B3
    B1 --> B4

    B2 --> C1
    B2 --> C2
    B2 --> C3
    B3 --> C1
    B3 --> C2
    B4 --> C4
    B4 --> C5

    C1 --> D1
    C2 --> D1
    C3 --> D1
    C4 --> D1
    C5 --> D2
    C5 --> D3

    style A1 fill:#e1f5ff
    style B1 fill:#fff4e1
    style C1 fill:#ffe1e1
    style D1 fill:#e1ffe1
```

---

## 3. Attention Pipeline

Multi-head attention forward pass with detailed kernel flow.

```mermaid
flowchart TD
    Start(["Input Tensor
    batch, seq_len, hidden_dim"]) --> QKV["Linear Projection Kernels
    Q = X*W_q + b_q
    K = X*W_k + b_k
    V = X*W_v + b_v"]

    QKV --> Reshape["Reshape for Multi-Head
    batch, seq, hidden → batch, heads, seq, head_dim"]

    Reshape --> Scores["Compute Attention Scores
    scores = Q*K_T / sqrt(head_dim)"]

    Scores --> Mask{"Causal
    Masking?"}

    Mask -->|Yes| MaskApply["Apply Causal Mask
    scores[i,j] = -inf if j > i"]
    Mask -->|No| Softmax
    MaskApply --> Softmax["Softmax Kernel
    exp normalization"]

    Softmax --> Apply["Apply Attention
    output = softmax(scores)*V"]

    Apply --> Transpose["Transpose Back
    batch, heads, seq, head_dim → batch, seq, hidden"]

    Transpose --> Output["Output Projection
    out = concat*W_o + b_o"]

    Output --> End(["Output Tensor
    batch, seq_len, hidden_dim"])

    subgraph "Kernel Launches (7 steps)"
        QKV
        Reshape
        Scores
        MaskApply
        Softmax
        Apply
        Transpose
        Output
    end

    subgraph "Memory Layout"
        M1["Q, K, V Projections
        batch*seq × hidden"]
        M2["Q_heads, K_heads, V_heads
        batch × heads × seq × head_dim"]
        M3["Attention Scores
        batch × heads × seq × seq"]
        M4["Attention Output
        batch × heads × seq × head_dim"]
    end

    QKV -.allocate.- M1
    Reshape -.allocate.- M2
    Scores -.allocate.- M3
    Apply -.allocate.- M4

    style Start fill:#e1f5ff
    style End fill:#e1ffe1
    style QKV fill:#ffe1e1
    style Scores fill:#ffe1e1
    style Softmax fill:#ffe1e1
    style Apply fill:#ffe1e1
```

**Performance Characteristics:**

- **Memory Usage**: O(batch × seq² × heads) for attention scores (dominant)
- **Compute**: O(batch × seq² × hidden) for score computation
- **Kernel Launches**: 7 kernels total (can be fused for better performance)

---

## 4. Mixture of Experts Flow

Expert routing and dynamic loading pipeline.

```mermaid
flowchart TD
    Start(["Input
    batch, seq_len, hidden_dim"]) --> Router["Router Network
    scores = X*W_router"]

    Router --> TopK["Top-K Selection
    Select top-k experts per token"]

    TopK --> Normalize["Normalize Routing Weights
    softmax over selected experts"]

    Normalize --> Check{"Dynamic
    Loading?"}

    Check -->|Yes| Load["Load Expert Weights from NVMe
    For each active expert:
    1. Calculate offset
    2. O_DIRECT read to pinned memory
    3. cudaMemcpy to GPU"]
    Check -->|No| Cache["Use Cached Weights
    All experts in GPU memory"]

    Load --> Execute
    Cache --> Execute["Execute Expert FFN
    For each token:
    1. Route to top-k experts
    2. out_i = GELU(x*w1_i)*w2_i
    3. Weighted combination"]

    Execute --> Combine["Combine Expert Outputs
    out = Σ(weight_i × expert_output_i)"]

    Combine --> End(["Output
    batch, seq_len, hidden_dim"])

    subgraph "NVMe Layout"
        N1["Expert 0 Weights
        w1, w2, b1, b2"]
        N2["Expert 1 Weights
        w1, w2, b1, b2"]
        N3["Expert N Weights
        w1, w2, b1, b2"]
    end

    subgraph "Routing Info"
        R1["expert_indices
        batch*seq × k"]
        R2["routing_weights
        batch*seq × k"]
        R3["expert_capacity
        num_experts"]
    end

    Load -.read.- N1
    Load -.read.- N2
    Load -.read.- N3

    TopK -.produce.- R1
    Normalize -.produce.- R2
    Execute -.update.- R3

    style Start fill:#e1f5ff
    style End fill:#e1ffe1
    style Router fill:#ffe1e1
    style Execute fill:#ffe1e1
    style Load fill:#fff4e1
```

**Expert Loading Strategies:**

| Mode | GPU Memory | NVMe I/O | Use Case |
|------|-----------|----------|----------|
| **ALL_IN_MEMORY** | High (all experts) | None | Small models, low latency |
| **DYNAMIC_FFN_ONLY** | Medium (active experts) | Low | Medium models, balanced |
| **DYNAMIC_ALL** | Low (minimal cache) | High | Large models, memory constrained |

---

## 5. PyTorch Dispatcher Integration

Shows how dispatcher keys enable autograd, AMP, and torch.compile.

```mermaid
graph TB
    subgraph "User Code"
        A["Python: attn = MultiHeadAttention
        output = attn(input)"]
    end

    subgraph "PyTorch Dispatcher"
        B["Dispatcher Lookup
        attention_expert::attention_forward"]
        C{"Dispatch Key
        Selection"}
    end

    subgraph "Dispatch Keys"
        D1["Autograd Key
        AttentionAutogradFunction"]
        D2["Autocast Key
        FP16/BF16 Casting"]
        D3["CUDA Key
        attention_forward_impl"]
        D4["CPU Key
        Fallback Implementation"]
    end

    subgraph "Autograd Handling"
        E1["Forward Pass
        Save tensors for backward"]
        E2["Backward Pass
        Compute gradients"]
        E3["Redispatch to CUDA
        Call actual kernel"]
    end

    subgraph "CUDA Implementation"
        F1["Input Validation
        Check shapes, types"]
        F2["Setup Config
        AttentionConfig struct"]
        F3["Call CUDA Kernel
        attention_forward_cuda"]
        F4["Return Output
        PyTorch tensor"]
    end

    A --> B
    B --> C

    C -->|requires_grad=True| D1
    C -->|autocast enabled| D2
    C -->|CUDA device| D3
    C -->|CPU device| D4

    D1 --> E1
    E1 --> E3
    E3 --> D3
    D1 -.backward call.- E2

    D2 --> F1
    D3 --> F1
    F1 --> F2
    F2 --> F3
    F3 --> F4

    F4 --> A

    style A fill:#e1f5ff
    style C fill:#fff4e1
    style D1 fill:#ffe1e1
    style D2 fill:#ffe1e1
    style D3 fill:#ffe1e1
    style F3 fill:#ffd4d4
```

**Dispatcher Benefits:**

1. **Autograd**: Automatic differentiation without manual gradient registration
2. **AMP**: Transparent FP16/BF16 casting for 2x speedup
3. **torch.compile**: Graph-level optimization and fusion
4. **CUDA Graphs**: Kernel launch overhead elimination
5. **Multi-GPU**: Device guards ensure correct GPU routing

---

## 6. NVMe Tensor Loader

Architecture for direct NVMe-to-GPU data loading.

```mermaid
flowchart TB
    subgraph "Python API"
        A1["read_tensor
        device_path, offset, shape, dtype"]
        A2["write_tensor
        tensor, device_path, offset"]
        A3["TensorNVMeReader
        Dictionary-based access"]
    end

    subgraph "C++ Implementation"
        B1["read_tensor
        1. Allocate GPU tensor
        2. Call read_into_tensor"]
        B2["read_into_tensor
        1. Open NVMe with O_DIRECT
        2. posix_memalign aligned buffer
        3. pread from device
        4. cudaMemcpy to GPU"]
        B3["write_tensor
        1. cudaMemcpy to host
        2. pwrite to device
        3. Free host buffer"]
    end

    subgraph "TensorNVMeReader Logic"
        C1["add_kind
        kind_id, start_lba, length, shape"]
        C2["read_kind
        kind_id, idx, count"]
        C3["Calculate Offset
        offset = start_lba + idx*item_size"]
        C4["Call read_tensor
        shape = count, *item_shape"]
    end

    subgraph "NVMe Device"
        D1[("Kind 0: Images
        LBA 0-50000")]
        D2[("Kind 1: Labels
        LBA 50000-100000")]
        D3[("Kind 2: Experts
        LBA 100000-200000")]
    end

    A1 --> B1
    A2 --> B3
    A3 --> C1
    A3 --> C2

    B1 --> B2
    C2 --> C3
    C3 --> C4
    C4 --> B1

    B2 -.O_DIRECT read.- D1
    B2 -.O_DIRECT read.- D2
    B2 -.O_DIRECT read.- D3
    B3 -.O_DIRECT write.- D3

    subgraph "Memory Path"
        E1[NVMe Device]
        E2[Aligned Host Buffer<br/>posix_memalign 4096]
        E3[GPU Tensor<br/>CUDA Memory]
    end

    E1 -->|pread| E2
    E2 -->|cudaMemcpy| E3

    style A1 fill:#e1f5ff
    style B2 fill:#fff4e1
    style D1 fill:#e1ffe1
    style E1 fill:#e1ffe1
```

**Key Features:**

- **O_DIRECT**: Bypasses page cache for consistent latency
- **Aligned I/O**: 4KB alignment required for O_DIRECT
- **Zero-Copy Path**: NVMe → Pinned Memory → GPU (no extra copies)
- **Dictionary Access**: Multiple data kinds with structured indexing

---

## 7. Data Structures

Relationships between key data structures.

```mermaid
classDiagram
    class AttentionConfig {
        +size_t batch_size
        +size_t seq_len
        +size_t num_heads
        +size_t head_dim
        +size_t hidden_dim
        +bool use_bias
        +float dropout
        +bool causal
    }

    class AttentionWeights {
        +float* q_weight
        +float* k_weight
        +float* v_weight
        +float* o_weight
        +float* q_bias
        +float* k_bias
        +float* v_bias
        +float* o_bias
    }

    class AttentionOutput {
        +float* output
        +float* attention_scores
    }

    class NVMeLoadConfig {
        +LoadMode mode
        +const char* nvme_path
        +uint64_t weight_offset
        +size_t weight_size_bytes
        +void* staging_buffer
        +bool use_pinned_memory
    }

    class ExpertConfig {
        +size_t num_experts
        +size_t experts_per_token
        +size_t hidden_dim
        +size_t ffn_dim
        +bool use_bias
        +float capacity_factor
        +bool normalize_scores
    }

    class ExpertWeights {
        +float* w1
        +float* w2
        +float* b1
        +float* b2
    }

    class RoutingInfo {
        +int* expert_indices
        +float* routing_weights
        +int* expert_capacity
    }

    class ExpertNVMeLayout {
        +uint64_t base_offset
        +size_t expert_size_bytes
        +size_t stride_bytes
        +get_expert_offset(expert_id)
    }

    class ExpertLoadConfig {
        +bool load_on_demand
        +const char* nvme_device_path
        +ExpertNVMeLayout layout
        +void** expert_cache_ptrs
        +bool* expert_loaded
        +size_t max_cached_experts
        +void* io_buffer
        +size_t io_buffer_size
    }

    class TensorNVMeReader {
        -string device_path_
        -map~int,KindInfo~ kinds_
        +add_kind(kind_id, start_lba, length, ...)
        +read_kind(kind_id, idx, count)
        +get_kind_length(kind_id)
    }

    class KindInfo {
        +int64_t start_lba
        +int64_t length
        +int64_t sector_size
        +int64_t item_size_bytes
        +ScalarType dtype
        +vector~int64_t~ item_shape
    }

    AttentionConfig --> AttentionWeights : uses
    AttentionConfig --> AttentionOutput : produces
    AttentionWeights --> NVMeLoadConfig : optional loading

    ExpertConfig --> ExpertWeights : uses
    ExpertConfig --> RoutingInfo : produces
    ExpertWeights --> ExpertNVMeLayout : storage layout
    ExpertLoadConfig --> ExpertNVMeLayout : contains

    TensorNVMeReader --> KindInfo : manages multiple

    style AttentionConfig fill:#e1f5ff
    style ExpertConfig fill:#fff4e1
    style TensorNVMeReader fill:#e1ffe1
```

---

## 8. File Organization

Project structure with component responsibilities.

```mermaid
graph TB
    subgraph "src/"
        A1[common/<br/>Data structures and configs]
        A2[kernels/<br/>CUDA kernel implementations]
        A3[pytorch/<br/>PyTorch integration layer]
    end

    subgraph "src/common/"
        B1[attention_types.h<br/>AttentionConfig, AttentionWeights<br/>NVMeLoadConfig, LoadMode]
        B2[expert_config.h<br/>ExpertConfig, ExpertWeights<br/>RoutingInfo, ExpertNVMeLayout]
    end

    subgraph "src/kernels/"
        C1[attention_fwd.cu<br/>Linear projections<br/>Attention scores computation<br/>Softmax, attention application]
        C2[expert_fwd.cu<br/>Router network<br/>Top-K expert selection<br/>Expert FFN execution]
    end

    subgraph "src/pytorch/"
        D1[attention_pytorch.cpp<br/>TORCH_LIBRARY registration<br/>Dispatcher implementations<br/>Autograd, Autocast support]
        D2[nvme_tensor_loader.cpp<br/>read_tensor, write_tensor<br/>TensorNVMeReader class<br/>O_DIRECT NVMe I/O]
    end

    subgraph "python/"
        E1[setup.py<br/>Build configuration]
        E2[attention_expert/<br/>__init__.py<br/>ops.py, nvme_loader.py]
        E3[examples/<br/>training_with_nvme.py]
    end

    subgraph "doxygen/"
        H1[Doxyfile.in<br/>Config template]
        H2[mainpage.md<br/>Architecture overview]
    end

    subgraph "test/unit/"
        F1[test_attention_types.cpp<br/>Validates metadata defaults]
        F2[test_expert_config.cpp<br/>NVMe layout math, cache toggles]
    end

    subgraph "test/integration/"
        G1[test_pytorch_integration.py<br/>PyTorch dispatcher + AMP]
        G2[test_nvme_loading.py<br/>TensorNVMeReader workflows]
    end

    A1 --> B1
    A1 --> B2
    A2 --> C1
    A2 --> C2
    A3 --> D1
    A3 --> D2

    B1 --> C1
    B2 --> C2
    C1 --> D1
    C2 --> D1
    D1 --> E2
    D2 --> E2
    E1 --> E2
    E2 --> E3

    E2 --> F1
    E2 --> F2
    E2 --> G1
    E2 --> G2
    H1 --> H2

    style A1 fill:#e1f5ff
    style A2 fill:#ffe1e1
    style A3 fill:#fff4e1
    style E1 fill:#e1ffe1
```

**Component Breakdown:**

| Directory | Lines of Code | Purpose |
|-----------|--------------|---------|
| `src/common/` | ~160 | Data structure definitions, no implementation |
| `src/kernels/` | ~600 | CUDA kernel implementations (attention + MoE) |
| `src/pytorch/` | ~600 | PyTorch dispatcher, autograd, NVMe loader |
| `python/` | ~200 | Python API, nn.Module wrappers, setup script |
| `test/` | ~400 | C++ metadata regression tests + PyTorch integration |

**Unit test focus (new):**
- `test/unit/common/test_attention_types.cpp` — guards constructor defaults and NVMe load flags exposed via headers.
- `test/unit/common/test_expert_config.cpp` — verifies NVMe layout math + load configuration bookkeeping used across host + device paths.

### Documentation Submodules (59.1–59.9)

To keep long-form docs maintainable, each major README section now has a sibling directory under the module root:

| Section | Directory | Purpose |
|---------|-----------|---------|
| Overview | `59.1_Overview/` | Layered summary + navigation hub (full module) |
| Features | `59.2_Features/` | Capability matrix + CUDA/host registry linked to 59.1 |
| Build & Install | `59.3_Build_and_Install/` | Executable build recipe + CLI/tests |
| Usage Examples | `59.4_Usage_Examples/` | Catalog of runnable snippets tied to real files |
| PyTorch Integration | `59.5_PyTorch_Integration/` | Dispatcher/autograd/AMP verification |
| Dynamic NVMe Loading | `59.6_Dynamic_NVMe_Loading/` | NVMe mode matrix + kernel validation |
| Performance | `59.7_Performance/` | Profiling scenarios + Nsight commands |
| Testing | `59.8_Testing/` | Test matrix referencing performance plan |
| NVMe Data Loading | `59.9_NVMe_Data_Loading/` | Dataset routes + TensorNVMeReader plan |

All nine directories now satisfy the Module 16+ structure (src/, test/, doxygen/, profiling hooks) and can be referenced by tooling/CI to keep documentation synchronized with code.

---

## Performance Optimization Opportunities

Based on the architecture, here are key optimization areas:

### 1. Kernel Fusion

**Current**: 7 separate kernel launches for attention
**Optimized**: Fuse into 2-3 kernels (Flash Attention style)
**Benefit**: ~2-3x speedup from reduced memory traffic

```mermaid
graph LR
    A[Current: 7 Kernels] -->|Fuse| B[Optimized: 2-3 Kernels]
    B --> C[Benefits:<br/>- Reduced memory I/O<br/>- Lower launch overhead<br/>- Better L1/L2 cache usage]

    style A fill:#ffe1e1
    style B fill:#e1ffe1
```

### 2. Expert Prefetching

**Current**: Load experts on-demand during forward pass
**Optimized**: Prefetch next batch's experts asynchronously
**Benefit**: Hide NVMe latency with computation

```mermaid
sequenceDiagram
    participant F as Forward Pass
    participant P as Prefetcher
    participant N as NVMe

    F->>F: Process Batch 0
    F->>P: Prefetch Batch 1 experts
    P->>N: Async read experts [5,7,12]
    F->>F: Process Batch 0 (continues)
    N-->>P: Experts ready
    F->>F: Process Batch 1 (experts already cached)

    Note over F,N: Computation and I/O overlap
```

### 3. Shared Memory Optimization

**Current**: Naive global memory access in attention
**Optimized**: Use shared memory for tile-based computation
**Benefit**: 5-10x faster for large sequences

---

## Conclusion

This architecture demonstrates production-quality PyTorch extension design with:

1. **Clean Layering**: Python → PyTorch → CUDA → Storage
2. **Native Integration**: Full dispatcher support (autograd, AMP, compile)
3. **Scalability**: Dynamic NVMe loading for extreme-scale models
4. **Performance**: Optimized CUDA kernels with fusion opportunities

For implementation details, see:
- [README.md](README.md) - User guide and API documentation
- [research/pytorch_cuda_extension_guide.md](research/pytorch_cuda_extension_guide.md) - Extension development guide
- [research/pytorch_advanced_integration.md](research/pytorch_advanced_integration.md) - Dispatcher patterns
