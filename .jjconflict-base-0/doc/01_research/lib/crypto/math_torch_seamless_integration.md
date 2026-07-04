# Math Block Seamless PyTorch Integration

**Date:** 2026-01-26
**Status:** Research
**Related:** `math_block_design.md`, `pytorch_integration.md`, `math.md`

## Executive Summary

This document explores how to make Simple's `m{}` math blocks work seamlessly with PyTorch, enabling:
1. **Normal mode**: Regular computation without gradient tracking (fast, memory-efficient)
2. **Differentiable mode**: Automatic gradient tracking for loss/backpropagation (PyTorch autograd)

The key insight is to use a **dual-mode tensor type** that transparently switches between eager NumPy-like computation and PyTorch's computation graph based on context.

---

## 1. Problem Statement

Currently, math blocks support mathematical expressions:

```simple
m{
    y = A' @ x + b                 # Linear transform
    loss = (y - target)^2.mean()  # MSE loss
}
```

**Challenge**: How do we make this code work for both:
- **Inference**: Fast computation, no gradient tracking
- **Training**: Full autograd support, backpropagation

---

## 2. Design Goals

| Goal | Description |
|------|-------------|
| **Seamless syntax** | Same `m{}` syntax for both modes |
| **Zero-copy PyTorch** | Use PyTorch tensors directly when differentiable |
| **Lazy differentiation** | Only build computation graph when needed |
| **Efficient loss** | Minimize overhead for loss computation |
| **Composable** | Works with existing tensor operations |

---

## 3. Proposed Architecture

### 3.1 Dual-Mode Tensor

```simple
enum TensorMode:
    Eager       # NumPy-like, no gradient tracking
    Differentiable  # PyTorch autograd enabled

struct DualTensor<T, const N: i64>:
    """Tensor that can switch between eager and differentiable modes."""
    _mode: TensorMode
    _eager_data: Option<EagerTensor<T, N>>      # For fast inference
    _torch_data: Option<TorchTensor>            # For backprop
    _requires_grad: bool
```

### 3.2 Mode Detection

The system automatically detects when differentiation is needed:

```simple
# Context determines mode
with autograd.no_grad():
    # Eager mode - fast inference
    val y = m{ A @ x + b }  # Uses EagerTensor internally

with autograd.enable_grad():
    # Differentiable mode - builds computation graph
    val y = m{ A @ x + b }  # Uses TorchTensor internally
    y.backward()            # Backpropagation works
```

---

## 4. Loss Expression Patterns

### 4.1 Explicit Loss Block

A new `loss{}` block that explicitly marks differentiable computation:

```simple
# Training loop
for batch in data_loader:
    val (x, target) = batch

    # Forward pass (inside loss{} block = differentiable)
    val total_loss = loss{
        val y = A @ x + b
        val pred = y.softmax(dim: 1)
        -target * pred.log().sum(dim: 1).mean()  # Cross-entropy
    }

    # Backward pass
    total_loss.backward()
    optimizer.step()
```

**Benefits:**
- Clear visual distinction between inference and training code
- Compiler can optimize: only build graph inside `loss{}`
- Matches mental model: "this is where we compute loss"

### 4.2 Inline Loss with `requires_grad`

Alternative: Mark tensors explicitly:

```simple
# Parameters with gradients
val W = torch.randn([10, 5], requires_grad: true)
val b = torch.zeros([5], requires_grad: true)

# Forward pass - auto-detects differentiable mode
val y = m{ W @ x + b }
val loss = m{ (y - target)^2.mean() }

loss.backward()  # Works because W, b have requires_grad=true
```

### 4.3 Functional Loss (JAX-style)

Inspired by JAX's functional approach:

```simple
# Define model as pure function
fn forward(params: ModelParams, x: Tensor) -> Tensor:
    val {W, b} = params
    m{ W @ x + b }

# Define loss as pure function
fn compute_loss(params: ModelParams, x: Tensor, target: Tensor) -> Tensor:
    val y = forward(params, x)
    m{ (y - target)^2.mean() }

# Get gradients using value_and_grad
val (loss_val, grads) = value_and_grad(compute_loss)(params, x, target)

# Update parameters
params = m{ params - lr * grads }
```

**Benefits:**
- Purely functional, no mutation
- Easy to compose transformations (grad, vmap, jit)
- Works well with JAX interop

---

## 5. Efficient Backpropagation

### 5.1 Graph Construction Strategy

| Strategy | Description | Use Case |
|----------|-------------|----------|
| **Eager** | No graph, immediate execution | Inference |
| **Lazy tracing** | Build graph on first backward | Training (default) |
| **Compiled graph** | JIT compile graph once | Production training |

### 5.2 Lazy Tracing Implementation

```simple
class LazyGraph:
    """Builds computation graph lazily on first backward pass."""
    operations: Vec<Operation>
    tensors: Vec<TensorRef>
    compiled: Option<CompiledGraph>

    fn record_op(op: Operation, inputs: [TensorRef], output: TensorRef):
        """Record operation during forward pass."""
        self.operations.push(op)
        # ... track dependencies

    fn backward(grad_output: Tensor):
        """Build and execute backward graph."""
        if not self.compiled.?:
            self.compiled = Some(self.compile_backward())
        self.compiled.unwrap().execute(grad_output)
```

### 5.3 Gradient Checkpointing

For large models, trade compute for memory:

```simple
# Checkpoint large intermediate activations
val y = checkpoint{
    val h1 = m{ relu(W1 @ x + b1) }
    val h2 = m{ relu(W2 @ h1 + b2) }
    val h3 = m{ relu(W3 @ h2 + b3) }
    h3
}

# During backward, h1, h2, h3 are recomputed (not stored)
y.backward()
```

---

## 6. PyTorch Interop Details

### 6.1 Zero-Copy Tensor Sharing

```simple
# Simple tensor → PyTorch (zero-copy via DLPack)
val simple_tensor = m{ randn([100, 100]) }
val torch_tensor = simple_tensor.to_torch()  # Zero-copy

# PyTorch tensor → Simple (zero-copy)
val back = Tensor.from_torch(torch_tensor)  # Zero-copy
```

### 6.2 Autograd Bridge

```simple
# Custom autograd function for Simple operations
class SimpleMathFunction(torch.autograd.Function):
    @staticmethod
    fn forward(ctx: Context, *inputs: Tensor) -> Tensor:
        ctx.save_for_backward(*inputs)
        # Execute Simple m{} expression
        return execute_math_block(inputs)

    @staticmethod
    fn backward(ctx: Context, grad_output: Tensor) -> Tuple<Tensor>:
        inputs = ctx.saved_tensors
        # Compute gradients for each input
        return compute_math_grads(grad_output, inputs)
```

### 6.3 Compilation Modes

| Mode | Description | Command |
|------|-------------|---------|
| **Eager** | Direct PyTorch execution | Default |
| **torch.compile** | PyTorch 2.0+ JIT | `@torch_compile` |
| **TorchScript** | Export for C++/mobile | `.to_torchscript()` |
| **ONNX** | Cross-framework export | `.to_onnx()` |

---

## 7. Syntax Proposals

### 7.1 Option A: `loss{}` Block

```simple
# Explicit loss computation block
val loss = loss{
    y = model(x)
    cross_entropy(y, target)
}
loss.backward()
```

**Pros:** Clear intent, compiler can optimize
**Cons:** New syntax, verbosity

### 7.2 Option B: `diff{}` Block

```simple
# Differentiable computation block
val y = diff{
    A @ x + b
}
val loss = diff{ (y - target)^2.mean() }
```

**Pros:** More general than just loss
**Cons:** Less intuitive name

### 7.3 Option C: Context Manager (Python-like)

```simple
# Use existing with/autograd pattern
with autograd.record():
    val y = m{ A @ x + b }
    val loss = m{ (y - target)^2.mean() }
    loss.backward()
```

**Pros:** Familiar to PyTorch users, no new syntax
**Cons:** Verbose, easy to forget

### 7.4 Option D: Implicit Mode Detection (Recommended)

```simple
# System auto-detects based on tensor properties
val W = param([10, 5])  # Parameters have requires_grad=true
val b = param([5])

# This automatically uses differentiable mode because W, b require grad
val y = m{ W @ x + b }
val loss = m{ (y - target)^2.mean() }
loss.backward()

# This uses eager mode because no tensors require grad
with no_grad():
    val predictions = m{ W @ test_x + b }  # Fast inference
```

**Pros:** Minimal syntax, follows PyTorch convention
**Cons:** Implicit behavior may confuse users

---

## 8. Implementation Plan

### Phase 1: Dual-Mode Tensor (2 weeks)

1. Implement `TensorMode` enum
2. Add mode tracking to tensor struct
3. Implement eager vs differentiable dispatch
4. Tests for mode switching

### Phase 2: Autograd Bridge (3 weeks)

1. Implement `requires_grad` property
2. Build computation graph during forward
3. Implement backward pass
4. Support `torch.autograd.grad()`

### Phase 3: Loss Expression (2 weeks)

1. Implement `loss{}` or `diff{}` block (if chosen)
2. Add `value_and_grad()` functional API
3. Implement gradient checkpointing
4. Performance optimization

### Phase 4: Compilation (2 weeks)

1. torch.compile integration
2. TorchScript export
3. ONNX export
4. Benchmarking

---

## 9. Example: Complete Training Loop

```simple
import ml.torch as torch
import ml.torch.optim as optim
import ml.torch.data as data

# Model parameters
val W1 = param([784, 256])
val b1 = param([256])
val W2 = param([256, 10])
val b2 = param([10])

fn forward(x: Tensor) -> Tensor:
    m{
        h = relu(W1 @ x + b1)
        W2 @ h + b2
    }

fn compute_loss(x: Tensor, target: Tensor) -> Tensor:
    val logits = forward(x)
    m{ cross_entropy(logits, target) }

# Training
val optimizer = optim.Adam([W1, b1, W2, b2], lr: 0.001)

for epoch in 0..10:
    for (x, y) in train_loader:
        optimizer.zero_grad()

        val loss = compute_loss(x, y)
        loss.backward()

        optimizer.step()

    # Validation (no gradients)
    with no_grad():
        val val_loss = compute_loss(val_x, val_y)
        print "Epoch {epoch}: val_loss = {val_loss.item()}"
```

---

## 10. Comparison with Other Systems

| System | Approach | Pros | Cons |
|--------|----------|------|------|
| **PyTorch** | Dynamic graph, eager | Flexible, debuggable | Slower than compiled |
| **JAX** | Functional, trace-based | Composable transforms | Requires pure functions |
| **Swift for TF** | Language-integrated AD | Type-safe differentiation | Discontinued |
| **Julia Zygote** | Source transformation | Fast, general | Complex implementation |
| **Simple (proposed)** | Dual-mode, implicit | Best of PyTorch + JAX | Implementation complexity |

---

## 11. Open Questions

1. **Block syntax**: `loss{}` vs `diff{}` vs implicit mode?
2. **Higher-order derivatives**: Support Hessians, Jacobians?
3. **Custom gradients**: How to define custom backward rules?
4. **Distributed training**: How does this work with DDP?
5. **Mixed precision**: How to handle fp16/bf16 gradients?

---

## 12. Recommendations

1. **Start with implicit mode detection** (Option D) - minimal syntax change, follows PyTorch convention
2. **Add `loss{}` block later** as an optimization hint
3. **Implement `value_and_grad()`** for functional style
4. **Use DLPack** for zero-copy PyTorch interop
5. **Leverage torch.compile** for production performance

---

## 13. References

- [PyTorch Autograd Mechanics](https://docs.pytorch.org/docs/stable/notes/autograd.html)
- [JAX Autodiff Documentation](https://docs.jax.dev/en/latest/automatic-differentiation.html)
- [Swift for TensorFlow Differentiable Programming](https://github.com/tensorflow/swift/blob/main/docs/AutomaticDifferentiation.md)
- [Julia Zygote.jl](https://fluxml.ai/Zygote.jl/)
- [PyTorch torch.compile Tutorial](https://docs.pytorch.org/tutorials/intermediate/torch_compile_tutorial.html)

---

## Appendix A: Gradient Computation Rules

For each math operator, define gradient rules:

| Operator | Forward | Backward |
|----------|---------|----------|
| `+` | `z = x + y` | `dx = dz`, `dy = dz` |
| `-` | `z = x - y` | `dx = dz`, `dy = -dz` |
| `*` | `z = x * y` | `dx = y * dz`, `dy = x * dz` |
| `/` | `z = x / y` | `dx = dz / y`, `dy = -x * dz / y^2` |
| `^` | `z = x ^ n` | `dx = n * x^(n-1) * dz` |
| `@` | `z = A @ B` | `dA = dz @ B'`, `dB = A' @ dz` |
| `'` | `z = A'` | `dA = dz'` |
| `sum` | `z = x.sum()` | `dx = ones_like(x) * dz` |
| `mean` | `z = x.mean()` | `dx = ones_like(x) * dz / numel(x)` |

## Appendix B: Performance Considerations

| Scenario | Recommendation |
|----------|----------------|
| Inference | Use `no_grad()` context |
| Training | Default differentiable mode |
| Large batches | Consider gradient checkpointing |
| Production | Use `torch.compile` |
| Memory-limited | Use mixed precision (fp16) |
| Multi-GPU | Use DDP with NCCL backend |
