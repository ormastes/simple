# Math Blocks Runtime Contract

**Date:** 2026-04-04
**Status:** Active
**Scope:** Defines exact runtime semantics for `m{}`, `loss{}`, and `nograd{}` blocks.

## 1. Semantic Table

| Block | Runtime Effect | Return Value | Gradient Action | Backend Requirement |
|-------|---------------|--------------|-----------------|---------------------|
| `m{}` | Evaluate math DSL expression | Expression result (scalar or tensor) | None | Any (pure math) |
| `loss{}` | Evaluate + call `rt_torch_autograd_backward(handle)` | Loss tensor handle (i64) | Automatic backward on block exit | Torch autograd backend |
| `nograd{}` | Bracket body with `no_grad_begin()`/`no_grad_end()` | Body result (unchanged) | Gradient tracking disabled | Torch autograd backend |

## 2. `m{}` — Math Evaluation Block

**Semantics:** Evaluate a math DSL expression and return its value. No gradient action.

**Supported operand types:**
- Scalars (i64, f64)
- Tensor handles (i64 handle to torch tensor)
- Mixed scalar/tensor expressions

**Compilation:** The body is lowered through standard HIR → MIR → codegen. Math-mode syntax features (^, ', @, implicit multiplication, broadcast operators) are desugared during parsing.

**No runtime hooks required.** `m{}` adds syntax, not runtime behavior.

## 3. `loss{}` — Gradient-Enabled Loss Block

**Semantics:** Evaluate a differentiable expression, then call backward() on the result.

**Contract chosen: automatic backward on block completion.**

The block:
1. Evaluates the body expression (expected to produce a gradient-capable tensor)
2. Calls `rt_torch_autograd_backward(body_result_handle)` on the result
3. Returns the body result (the loss tensor handle)

**Result value after backward:** The loss value tensor is returned unchanged. Gradients are accumulated in the `.grad` fields of all `requires_grad` tensors in the computation graph.

**Preconditions:**
- The body result must be a scalar tensor (0-d) or reducible to scalar for backward
- At least one tensor in the computation graph must have `requires_grad = true`

**Error behavior:**
- If the result is not gradient-capable, the torch runtime raises an error at the `backward()` call
- Non-differentiable values (plain scalars, integers) produce a runtime error

**MIR lowering:**
```
body_result = lower_block(body)
emit_call("rt_torch_autograd_backward", [body_result])
return body_result
```

## 4. `nograd{}` — Gradient Suppression Block

**Semantics:** Disable gradient tracking for the enclosed expression, restore on exit.

**Contract: balanced begin/end with nesting safety.**

The block:
1. Calls `rt_torch_autograd_no_grad_begin()` — disables gradient tracking
2. Evaluates the body
3. Calls `rt_torch_autograd_no_grad_end()` — restores prior state

**Nesting behavior:** The torch runtime maintains an internal reference counter. Nested `nograd{}` blocks each push/pop the counter, so the outer block's exit correctly restores tracking.

**Composition with `loss{}`:**
- `nograd{}` inside `loss{}`: The nograd subexpression does not record gradient ops, but the surrounding loss block's result can still call backward (on the parts outside nograd)
- `loss{}` after `nograd{}`: Normal gradient behavior resumes

**Failure safety:** After body lowering, every MIR block that can escape the nograd scope is patched with a `no_grad_end()` call inserted before its terminator. Escape paths include:
- `Return` terminators — from `?` operator or explicit `return`
- `Goto` terminators targeting blocks outside the scope — from `break`/`continue` to an enclosing loop

Panics/aborts are unrecoverable and cannot be guarded at this level.

**MIR lowering:**
```
scope_start = builder.next_block_id
emit_call("rt_torch_autograd_no_grad_begin", [])
blocks_before = builder.blocks.len()
body_result = lower_block(body)
emit_call("rt_torch_autograd_no_grad_end", [])     # success path

# Patch all escaping terminators:
for block in builder.blocks[blocks_before..]:
    if block.terminator is Return:
        block.instructions.push(Call("rt_torch_autograd_no_grad_end", []))
    elif block.terminator is Goto(target) and target.id < scope_start:
        block.instructions.push(Call("rt_torch_autograd_no_grad_end", []))
return body_result
```

## 5. Runtime Functions

| Function | Signature | Source | Effect |
|----------|-----------|--------|--------|
| `rt_torch_autograd_backward` | `(handle: i64) -> void` | `torch/ffi.spl:341` | Compute gradients via backpropagation |
| `rt_torch_autograd_zero_grad` | `(handle: i64) -> void` | `torch/ffi.spl:344` | Zero out accumulated gradients |
| `rt_torch_autograd_grad` | `(handle: i64) -> i64` | `torch/ffi.spl:347` | Retrieve gradient tensor handle |
| `rt_torch_autograd_no_grad_begin` | `() -> void` | `torch/ffi.spl:350` | Enter no-grad context |
| `rt_torch_autograd_no_grad_end` | `() -> void` | `torch/ffi.spl:353` | Exit no-grad context |

## 6. Supported Backends

| Backend | `m{}` | `loss{}` | `nograd{}` | Compiled Proof |
|---------|-------|----------|------------|----------------|
| Pure scalar runtime | Stable | Not supported | Not supported | Yes |
| Torch autograd | Stable | Stable | Stable | Yes |
| CUDA (via torch) | Stable | Stable | Stable | Requires GPU |
| Other backends | Partial | Not supported | Not supported | No |

## 7. Non-Goals

- Full production deep-learning framework is NOT required
- Automatic differentiation of arbitrary Simple functions is out of scope
- Custom autograd function definition is not part of this contract
