# Autograd Interpreter Limitation - Copy vs Reference Semantics

## Problem

The current autograd implementation cannot work in the Simple interpreter due to **value semantics** for arrays:

```simple
var c = Counter(count: 0)
var arr = [c]              # Copies c into array
arr[0].increment()         # Modifies the COPY, not original
# c.count is still 0 !
```

## Impact on Autograd

```simple
class Tensor:
    inputs: [Tensor]?      # Stores COPIES of input tensors
    
fn propagate_grads(t: Tensor, grad_out: TensorF64):
    val inputs = t.inputs.unwrap()
    inputs[0].backward_step(grad_out)   # Modifies a COPY!
    # Original tensor never gets gradient
```

## Why This Happens

1. x creates a Tensor with requires_grad=true
2. tensor_mul_scalar(x, 2.0) creates y
3. y.inputs = Some([x])  ← x is COPIED into array
4. backward(y) calls inputs[0].backward_step()
5. This modifies the COPY in the array, not original x
6. x.grad remains None

## Solutions

### Option A: Global Gradient Store (Recommended for Interpreter)
```simple
# Global dict to store gradients
var GRADIENTS: Dict<i64, TensorF64> = {}

class Tensor:
    tensor_id: i64         # Unique ID
    # Remove inputs array, build graph separately
```

### Option B: Return Gradients (Functional Style)
```simple
fn backward(t: Tensor) -> Dict<i64, TensorF64>:
    # Return dict of tensor_id -> gradient
    # Caller applies gradients
```

### Option C: Accept Limitation (Document & Move On)
- Document that autograd needs compiled mode
- Focus on features that work in interpreter:
  - TensorF64 operations ✅
  - Forward pass ✅  
  - Manual gradient implementation ✅

## Recommendation

**Option C** for now:
1. Document the limitation clearly
2. Continue with other DL features (nn layers, optimizers) using manual gradients
3. Autograd will work perfectly in compiled mode
4. Revisit if/when interpreter gets reference semantics

This aligns with "pure simple, no rust" - we can't fix value semantics without Rust changes.
