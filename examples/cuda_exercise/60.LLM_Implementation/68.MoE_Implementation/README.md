# Part 68: MoE Implementation

**Goal**: Implement the Mixture-of-Experts (MoE) architecture with top-k routing, expert dispatch/combine, and load balancing auxiliary loss, enabling sparse scaling of transformer models.

## Project Structure

```
68.MoE_Implementation/
├── CMakeLists.txt
├── README.md
├── doxygen/
│   ├── Doxyfile.in
│   └── mainpage.md
├── src/
│   ├── CMakeLists.txt
│   ├── common/
│   │   ├── expert_network.h       # Expert weights and forward pass
│   │   ├── topk_router.h          # Router config and top-k selection
│   │   ├── moe_layer.h            # Complete MoE layer interface
│   │   └── moe_transformer.h      # MoE transformer config
│   └── kernels/
│       ├── router_kernels.cu      # Softmax gating + top-k selection
│       ├── expert_dispatch.cu     # Token scatter + expert FFN
│       ├── expert_combine.cu      # Weighted gather + MoE pipeline
│       └── load_balance_loss.cu   # Auxiliary loss for balanced usage
└── test/
    ├── CMakeLists.txt
    └── unit/
        └── kernels/
            ├── test_router.cu       # Router correctness tests
            ├── test_dispatch.cu     # Expert dispatch/combine tests
            └── test_moe_layer.cu    # End-to-end MoE layer tests
```

## Quick Navigation

- [68.1 MoE Architecture Overview](#681-moe-architecture-overview)
- [68.2 Top-K Expert Routing](#682-top-k-expert-routing)
- [68.3 Expert Dispatch](#683-expert-dispatch)
- [68.4 Expert Combine](#684-expert-combine)
- [68.5 Load Balance Loss](#685-load-balance-loss)
- [68.6 Summary](#686-summary)
- [Build & Run](#build--run)

---

## **68.1 MoE Architecture Overview**

Mixture-of-Experts replaces the dense FFN in transformer layers with a collection of expert networks, where only a subset of experts process each token. This allows scaling model parameters without proportional increase in computation: a model with 8 experts and top-2 routing uses only 2/8 = 25% of FFN compute per token.

### **68.1.1 MoE Layer Pipeline**

The MoE layer executes four stages:

```
Input tokens -> Router (top-k gating) -> Dispatch (scatter to experts)
  -> Expert FFN (parallel) -> Combine (weighted gather) -> Output
```

### **68.1.2 DeepSeek R1 Configuration**

In DeepSeek R1, the first few transformer layers use dense FFN and the remaining layers use MoE:

```cpp
// moe_transformer.h
MoETransformerConfig config(deepseek_7b(), first_moe_layer=1, aux_loss_weight=0.01);
bool use_moe = is_moe_layer(layer_idx, config);  // true for layer >= 1
```

**Source**: `src/common/moe_transformer.h`

---

## **68.2 Top-K Expert Routing**

The router is a learned gating network that assigns each token to its best-matching experts. It computes a softmax distribution over experts and selects the top-k.

### **68.2.1 Gating Computation**

```
gate_logits = input * W_gate^T     [num_tokens, num_experts]
gate_probs  = softmax(gate_logits)  [num_tokens, num_experts]
top_k_indices, top_k_weights = topk(gate_probs, k)
top_k_weights = renormalize(top_k_weights)  // sum to 1
```

### **68.2.2 Implementation**

```cpp
// router_kernels.cu - Three-stage routing pipeline
router_gate_kernel();    // Matrix multiply for gate logits
router_softmax_kernel(); // Per-token softmax normalization
router_topk_kernel();    // Top-k selection with renormalization
```

**Key Points**:
- Softmax is computed per-token with max-subtraction for numerical stability
- Top-k selection uses repeated max finding (efficient for small num_experts)
- Selected weights are renormalized to sum to 1 for proper weighted combination

**Source**: `src/kernels/router_kernels.cu`, `src/common/topk_router.h`

---

## **68.3 Expert Dispatch**

After routing, tokens must be scattered to their assigned experts' input buffers. Each token may be sent to multiple experts (top-k > 1), creating copies.

### **68.3.1 Dispatch Kernel**

```cpp
// expert_dispatch.cu
__global__ void expert_dispatch_kernel(
    expert_inputs,   // [num_experts, capacity, d_model]
    expert_counts,   // Atomic counters per expert
    input, expert_indices, ...
);
```

### **68.3.2 Expert Forward**

Each expert runs a SwiGLU FFN (shared architecture, independent weights):

```
output = W_down * (SiLU(W_gate * x) * (W_up * x))
```

**Key Points**:
- Atomic counters track how many tokens are assigned to each expert
- Capacity factor limits maximum tokens per expert to prevent overflow
- Expert forward reuses the SwiGLU architecture from Module 67

**Source**: `src/kernels/expert_dispatch.cu`, `src/common/expert_network.h`

---

## **68.4 Expert Combine**

The combine step gathers expert outputs and computes a weighted sum using the router weights, producing the final MoE layer output.

### **68.4.1 Weighted Gather**

```cpp
// expert_combine.cu
output[token] = sum_k(weight[token][k] * expert_output[selected_k][token])
```

### **68.4.2 Full Pipeline**

The `moe_layer_forward()` function orchestrates the complete pipeline:

```cpp
// moe_layer.h - Complete MoE layer
moe_layer_forward(output, input, W_router, experts, config,
                  num_tokens, &aux_loss);
```

**Key Points**:
- Combine kernel uses one thread-block per token for coalesced memory access
- Weights from the router ensure smooth gradient flow through the gating network
- The complete pipeline handles routing, dispatch, forward, and combine in one call

**Source**: `src/kernels/expert_combine.cu`, `src/common/moe_layer.h`

---

## **68.5 Load Balance Loss**

Without regularization, the router may collapse to always selecting the same experts, leaving others unused. The auxiliary load balancing loss encourages uniform expert utilization.

### **68.5.1 Loss Formula**

```
L_aux = alpha * num_experts * sum_e(f_e * P_e)

where:
  f_e = fraction of tokens routed to expert e
  P_e = mean routing probability for expert e
  alpha = loss weight coefficient (e.g., 0.01)
```

### **68.5.2 Implementation**

```cpp
// load_balance_loss.cu
compute_expert_stats_kernel();   // Per-expert fraction and mean probability
load_balance_loss_kernel();      // L_aux = alpha * N * sum(f_e * P_e)
```

**Key Points**:
- The loss is minimized when all experts have equal fraction and probability (uniform distribution)
- A small alpha (0.01) provides regularization without dominating the main loss
- Expert importance scores can be monitored for debugging router collapse

**Source**: `src/kernels/load_balance_loss.cu`

---

## **68.6 Summary**

- **Key Takeaways**:
  - MoE enables sparse scaling: more parameters without proportional compute increase
  - Top-k routing selects the best experts per token with softmax gating
  - Expert dispatch/combine implements the scatter-gather pattern on GPU
  - Load balancing loss prevents expert collapse and ensures all experts are utilized

- **Performance Characteristics**:

| Component | Complexity | Notes |
|-----------|-----------|-------|
| Router gate | O(tokens * experts * d_model) | Single matmul |
| Softmax + top-k | O(tokens * experts) | Per-token, small experts count |
| Expert forward | O(tokens/experts * d_model * d_ff) | Parallelizable across experts |
| Combine | O(tokens * top_k * d_model) | Weighted sum |

- **Common Errors**:

| Error | Cause | Solution |
|-------|-------|----------|
| Expert collapse | All tokens routed to same expert | Increase aux_loss_weight |
| Capacity overflow | Too many tokens per expert | Increase capacity_factor |
| NaN in routing weights | Large gate logits | Check W_gate initialization scale |
| Uneven GPU utilization | Imbalanced expert loads | Monitor per-expert token counts |

- **Next Steps**: [69.MoE_NVMe_Complete_System](../69.MoE_NVMe_Complete_System/README.md) - Integrate MoE with NVMe expert offloading

- **References**:
  - [DeepSeek R1 Paper](https://arxiv.org/abs/2401.02954)
  - [Switch Transformers (Fedus et al., 2022)](https://arxiv.org/abs/2101.03961) - Simplified MoE routing
  - [GShard (Lepikhin et al., 2021)](https://arxiv.org/abs/2006.16668) - Expert capacity and routing
  - [ST-MoE (Zoph et al., 2022)](https://arxiv.org/abs/2202.08906) - Router design and training stability

---

## Build & Run

```bash
# Build
cmake -B build -G Ninja
ninja -C build 68_MoE_Implementation_test

# Run tests
./build/60.LLM_Implementation/68.MoE_Implementation/test/68_MoE_Implementation_test

# Generate documentation
ninja -C build doxygen_68_MoE_Implementation
```
