# Dimension Error Guide

Quick reference for understanding and fixing dimension errors in Simple.

---

## Error Message Format

```
error[E0502]: layer dimension mismatch in ~> pipeline
  --> model.spl:15:23
   |
   = found: previous layer outputs shape: [batch, 256]
   = expected: next layer expects input shape: [batch, 128]
   = note: dimension 1 differs: 256 vs 128
   = help: insert Linear(256, 128) between these layers
```

### Components

| Part | Description |
|------|-------------|
| `error[E0502]` | Error code for lookup |
| `layer dimension mismatch...` | Brief description |
| `--> model.spl:15:23` | File, line, column |
| `= found:` | What was actually there |
| `= expected:` | What was required |
| `= note:` | Additional context |
| `= help:` | Suggested fix |

---

## Common Errors and Fixes

### E0501: Dimension Mismatch

**Cause**: Two dimensions don't match where they should.

```simple
# Error
val a: Tensor<f32, [32, 64]> = ...
val b: Tensor<f32, [32, 128]> = ...
val c = a + b  # E0501: 64 != 128
```

**Fix**: Ensure dimensions match or use broadcasting.

```simple
# Option 1: Reshape
val b_reshaped = b.reshape([32, 64])
val c = a + b_reshaped

# Option 2: Use correct dimensions from start
val b: Tensor<f32, [32, 64]> = ...
```

---

### E0502: Layer Incompatible

**Cause**: Layer output shape doesn't match next layer's input.

```simple
# Error
val model = Linear(784, 256) ~> Linear(128, 64)
# E0502: output [batch, 256] != input [batch, 128]
```

**Fix**: Insert matching layer or fix dimensions.

```simple
# Option 1: Add intermediate layer
val model = Linear(784, 256) ~> Linear(256, 128) ~> Linear(128, 64)

# Option 2: Fix the second layer
val model = Linear(784, 256) ~> Linear(256, 64)
```

---

### E0503: Rank Mismatch

**Cause**: Tensors have different number of dimensions.

```simple
# Error: 4D tensor to 2D layer
val conv_out: Tensor<f32, [batch, 64, 7, 7]> = ...
val fc = Linear(64, 10)
val out = conv_out ~> fc  # E0503: 4D vs 2D
```

**Fix**: Flatten or reshape before the layer.

```simple
val conv_out: Tensor<f32, [batch, 64, 7, 7]> = ...
val model = Flatten() ~> Linear(3136, 10)  # 64*7*7 = 3136
val out = conv_out |> model
```

---

### E0504: MatMul Incompatible

**Cause**: Inner dimensions don't match for matrix multiplication.

```simple
# Error
val A: Tensor<f32, [32, 64]> = ...
val B: Tensor<f32, [128, 256]> = ...
val C = A @ B  # E0504: 64 != 128
```

**Rule**: For `A @ B`, A's last dim must equal B's second-to-last.
- `[M, K] @ [K, N]` → `[M, N]`

**Fix**: Transpose or reshape.

```simple
# Option 1: Transpose B
val C = A @ B.T  # [32, 64] @ [256, 128].T = [32, 64] @ [128, 256] - still wrong!

# Option 2: Use correct dimensions
val B: Tensor<f32, [64, 256]> = ...
val C = A @ B  # [32, 64] @ [64, 256] = [32, 256] ✓
```

---

### E0505: Broadcast Incompatible

**Cause**: Shapes cannot be broadcast together.

```simple
# Error
val a: Tensor<f32, [3, 4]> = ...
val b: Tensor<f32, [5, 4]> = ...
val c = a .+ b  # E0505: 3 vs 5 (neither is 1)
```

**Broadcasting Rules**:
1. Align shapes from the right
2. Each dim must be equal OR one of them is 1
3. Missing dims treated as 1

**Fix**: Reshape to make broadcastable.

```simple
# Option 1: Expand to match
val a: Tensor<f32, [1, 3, 4]> = ...
val b: Tensor<f32, [5, 1, 4]> = ...
val c = a .+ b  # [5, 3, 4] ✓

# Option 2: Use same shape
val a: Tensor<f32, [5, 4]> = ...
val b: Tensor<f32, [5, 4]> = ...
```

---

### E0506: Batch Mismatch

**Cause**: Operations on tensors with different batch sizes.

```simple
# Error
val x: Tensor<f32, [32, 784]> = ...
val y: Tensor<f32, [64, 784]> = ...
val z = x + y  # E0506: batch 32 vs 64
```

**Fix**: Ensure consistent batch sizes.

```simple
val x: Tensor<f32, [32, 784]> = ...
val y: Tensor<f32, [32, 784]> = ...  # Same batch
val z = x + y  # ✓
```

---

### E0507: Channel Mismatch (CNN)

**Cause**: Conv layer's in_channels doesn't match input.

```simple
# Error
val x: Tensor<f32, [batch, 3, 224, 224]> = ...  # RGB (3 channels)
val conv = Conv2d(1, 32, 3)  # Expects 1 channel!
# E0507: Conv2d expects 1 input channels, got 3
```

**Fix**: Match in_channels to input.

```simple
val x: Tensor<f32, [batch, 3, 224, 224]> = ...
val conv = Conv2d(3, 32, 3)  # 3 input channels ✓
```

---

### E0508: Sequence Mismatch

**Cause**: Sequence lengths don't match in RNN/Transformer.

```simple
# Error
val encoder_out: Tensor<f32, [batch, 512, hidden]> = ...
val decoder_in: Tensor<f32, [batch, 256, hidden]> = ...
# E0508: sequence 512 vs 256
```

**Fix**: Pad/truncate sequences or use attention.

```simple
# Option 1: Pad shorter sequence
val decoder_in = pad(decoder_in, target_len=512)

# Option 2: Use cross-attention (handles different lengths)
val attn = CrossAttention(hidden)
val out = attn(query=decoder_in, key=encoder_out, value=encoder_out)
```

---

### E0509: Out of Range

**Cause**: Dimension value outside allowed range.

```simple
# Error with constraint: batch: 1..128
val x: Tensor<f32, [256, 784]> = ...  # batch=256
# E0509: dimension 256 outside range [1, 128]
```

**Fix**: Use value within range.

```simple
val x: Tensor<f32, [64, 784]> = ...  # batch=64 ✓
```

---

### E0510: Unresolved Variable

**Cause**: Cannot infer a dimension.

```simple
# Error
fn mystery<N>(x: Tensor<f32, [N, 784]>) -> Tensor<f32, [N, 10]>:
    # N is never constrained
```

**Fix**: Add type annotation or use concrete values.

```simple
# Option 1: Annotate at call site
val out = mystery<32>(input)

# Option 2: Add constraint
fn mystery<N>(x: Tensor<f32, [N, 784]>) -> Tensor<f32, [N, 10]>
where N: 1..128:
    ...
```

---

## Debugging Tips

### 1. Print Shapes

```simple
print "Input shape: {x.shape}"
print "After conv: {conv_out.shape}"
print "After flatten: {flat.shape}"
```

### 2. Use Explicit Types

```simple
# Add type annotations to catch errors early
val encoder: Layer<[batch, 784], [batch, 64]> = ...
val decoder: Layer<[batch, 64], [batch, 784]> = ...
```

### 3. Check Common Pitfalls

| Mistake | Fix |
|---------|-----|
| Forgot `Flatten()` before Linear | Add `Flatten()` layer |
| Wrong `in_channels` in Conv | Match to previous layer's `out_channels` |
| Batch dim in wrong position | Use `NCHW` or `NHWC` consistently |
| Kernel too large | Add padding or use smaller kernel |

### 4. Use Dimension Check Modes

```simple
# Development: Get detailed errors
val ctx = HmInferContext.with_dim_check_mode(DimCheckMode.Assert)

# Production: Skip checks for speed
val ctx = HmInferContext.with_dim_check_mode(DimCheckMode.None_)
```

---

## Quick Reference Table

| Error | Common Cause | Quick Fix |
|-------|--------------|-----------|
| E0501 | Different dimensions | Reshape/match dims |
| E0502 | Layer dims mismatch | Add intermediate layer |
| E0503 | Different ranks (ndim) | Flatten/reshape |
| E0504 | MatMul K mismatch | Transpose or reshape |
| E0505 | Can't broadcast | Add dims with unsqueeze |
| E0506 | Batch size differs | Use same batch size |
| E0507 | Wrong in_channels | Fix Conv2d params |
| E0508 | Sequence length differs | Pad/truncate |
| E0509 | Value out of range | Use valid value |
| E0510 | Can't infer dim | Add annotation |

---

## Getting Help

1. **Read the error carefully** - The `help:` line suggests a fix
2. **Check the shapes** - Print intermediate shapes
3. **Review layer docs** - Check expected input/output shapes
4. **Search error code** - `E05XX` in documentation
