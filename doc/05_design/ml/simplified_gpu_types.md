# Simplified GPU Types with Inference

**Feature ID**: #194
**Pattern**: Direct user enum + type inference (like async/Future)
**Date**: 2026-01-10

---

## Design Overview

Remove complexity by:
1. **No system enum** - User defines enum directly
2. **Type inference** - `@gpu(device)` wraps return type automatically
3. **Like async** - Similar to how `async fn` wraps in `Promise[T]`

```simple
# Simple: just define your device enum
enum UserGpu:
    Primary
    Secondary
    Inference
    Backup

# Type inference does the rest!
@gpu(Primary)
fn compute() -> Int:
    42  # Returns Gpu[Int, Primary] automatically!
```

---

## Complete Example

```simple
"""
GPU types with automatic type inference.
Like async/await, but for device placement.
"""

# ============================================================================
# Step 1: Define Device Enum (User-Defined)
# ============================================================================

enum UserGpu:
    """Application GPU roles."""
    Primary
    Secondary
    Inference
    Backup

# ============================================================================
# Step 2: Functions with @gpu Annotation
# ============================================================================

@gpu(Primary)
fn add(a: Int, b: Int) -> Int:
    """
    Declared return: Int
    Actual return: Gpu[Int, Primary] (inferred!)
    """
    a + b

@gpu(Secondary)
fn multiply(a: Int, b: Int) -> Int:
    """Returns Gpu[Int, Secondary] (inferred!)"""
    a * b

# ============================================================================
# Step 3: Automatic Wrapping (Like Async)
# ============================================================================

fn example_inference():
    # Call GPU function
    let x = add(10, 20)
    # Type inferred: Gpu[Int, Primary]

    let y = multiply(5, 6)
    # Type inferred: Gpu[Int, Secondary]

    # Operations stay on device
    let z = add(x, 5)  # x auto-unwraps in Primary context
    # Type: Gpu[Int, Primary]

# ============================================================================
# Step 4: Explicit Transfers When Needed
# ============================================================================

@gpu(Primary)
fn process_on_primary(data: Int) -> Int:
    data * 2

@gpu(Secondary)
fn process_on_secondary(data: Int) -> Int:
    data + 100

fn example_transfer():
    # Compute on Primary
    let x = process_on_primary(50)
    # Type: Gpu[Int, Primary]

    # Transfer to Secondary
    let y = x.to(Secondary)
    # Type: Gpu[Int, Secondary]

    # Compute on Secondary
    let z = process_on_secondary(y)
    # Type: Gpu[Int, Secondary]
```

---

## Type Inference Rules

### Rule 1: GPU Function Return Type

```
@gpu(device) fn foo() -> T
═══════════════════════════════
Actual return type: Gpu[T, device]
```

**Example:**
```simple
@gpu(Primary)
fn compute() -> Int:  # Declared: Int
    42

# Actual type: Gpu[Int, Primary]
```

### Rule 2: Auto-Unwrap in Same Device Context

```
x : Gpu[T, device]
Inside @gpu(device) function
═══════════════════════════════
x behaves as T (auto-unwrap)
```

**Example:**
```simple
@gpu(Primary)
fn process(x: Int) -> Int:  # x is Gpu[Int, Primary]
    x + 10  # x auto-unwraps to Int

let val = compute()  # Gpu[Int, Primary]
let result = process(val)  # val auto-unwraps
```

### Rule 3: Operations Stay on Device

```
x : Gpu[Int, device]
y : Gpu[Int, device]
In @gpu(device) context
═══════════════════════════════
x + y : Gpu[Int, device]
```

**Example:**
```simple
@gpu(Primary)
fn combine(a: Int, b: Int) -> Int:
    a + b  # Both auto-unwrap, result auto-wraps

let x = compute()  # Gpu[Int, Primary]
let y = compute()  # Gpu[Int, Primary]
let z = combine(x, y)  # Gpu[Int, Primary]
```

### Rule 4: Explicit Transfer Required for Different Devices

```
x : Gpu[T, device1]
Use in @gpu(device2) where device1 ≠ device2
═══════════════════════════════
ERROR: Device mismatch
Help: Use x.to(device2)
```

**Example:**
```simple
@gpu(Primary)
fn on_primary(x: Int) -> Int: x

@gpu(Secondary)
fn on_secondary(x: Int) -> Int: x

let x = on_primary(42)  # Gpu[Int, Primary]
let y = on_secondary(x)  # ❌ ERROR: Device mismatch
let y = on_secondary(x.to(Secondary))  # ✅ OK
```

---

## Comparison with Async/Await

| Feature | Async/Await | GPU Types |
|---------|-------------|-----------|
| **Annotation** | `async fn foo()` | `@gpu(device) fn foo()` |
| **Wrapping** | `-> T` becomes `Promise[T]` | `-> T` becomes `Gpu[T, device]` |
| **Unwrapping** | `await promise` | Auto in same device context |
| **Context** | Async function | GPU function with same device |
| **Effect** | May suspend | May transfer |
| **Type system** | Effect inference | Device inference |

### Async Example

```simple
async fn fetch_user(id: Int) -> User:
    ...  # Returns Promise[User] (inferred!)

let user_promise = fetch_user(123)  # Promise[User]
let user = await user_promise  # User
```

### GPU Example

```simple
@gpu(Primary)
fn compute_score(id: Int) -> Int:
    ...  # Returns Gpu[Int, Primary] (inferred!)

let score_gpu = compute_score(123)  # Gpu[Int, Primary]
let score = score_gpu.get()  # Int (explicit unwrap to host)
```

---

## Benefits

### 1. Simplicity

**Before:**
```simple
enum GpuIndex: Gpu0 | Gpu1 | Gpu2 | Gpu3
enum UserGpu[GpuIndex]: Primary | Secondary

impl From[UserGpu] for GpuIndex: ...

fn compute() -> Gpu[Int, UserGpu::Primary]:
    Gpu.new(42)
```

**After:**
```simple
enum UserGpu: Primary | Secondary

@gpu(Primary)
fn compute() -> Int:
    42
```

**Reduction**: 8 lines → 4 lines (50% less code!)

### 2. Readability

```simple
# Reads like normal code!
@gpu(Primary)
fn train_model(data: Tensor) -> Model:
    let features = extract_features(data)
    let model = build_model(features)
    train(model, data)

# All intermediate values automatically Gpu[T, Primary]
# No manual wrapping needed!
```

### 3. Type Safety

```simple
@gpu(Primary)
fn on_primary(x: Int) -> Int: x

@gpu(Secondary)
fn on_secondary(x: Int) -> Int: x

let x = on_primary(42)
let y = on_secondary(x)  # ❌ Compile error!
# Error: Cannot use Gpu[Int, Primary] in @gpu(Secondary)
# Help: Use x.to(Secondary)
```

### 4. Like Async (Familiar Pattern)

```simple
# Developers already understand this pattern:
async fn fetch() -> User: ...  # Returns Promise[User]

# Same mental model:
@gpu(Primary) fn compute() -> Int: ...  # Returns Gpu[Int, Primary]
```

---

## Advanced Examples

### Example 1: Multi-GPU Pipeline

```simple
@gpu(Primary)
fn stage1(data: Tensor) -> Tensor:
    preprocess(data)

@gpu(Secondary)
fn stage2(features: Tensor) -> Tensor:
    compute_features(features)

@gpu(Primary)
fn stage3(result: Tensor) -> Tensor:
    postprocess(result)

fn pipeline(input: Tensor):
    let stage1_out = stage1(input)  # Gpu[Tensor, Primary]

    let stage2_in = stage1_out.to(Secondary)  # Transfer
    let stage2_out = stage2(stage2_in)  # Gpu[Tensor, Secondary]

    let stage3_in = stage2_out.to(Primary)  # Transfer
    let final = stage3(stage3_in)  # Gpu[Tensor, Primary]

    final.to_host()  # Transfer to host
```

### Example 2: Data Parallel Training

```simple
@gpu(Primary)
fn train_batch_primary(batch: Tensor) -> Gradients:
    forward_backward(batch)

@gpu(Secondary)
fn train_batch_secondary(batch: Tensor) -> Gradients:
    forward_backward(batch)

fn data_parallel_train(data: List[Tensor]):
    let batch1 = data[0]
    let batch2 = data[1]

    # Parallel computation on different GPUs
    let grad1 = train_batch_primary(batch1)    # Gpu[Gradients, Primary]
    let grad2 = train_batch_secondary(batch2)  # Gpu[Gradients, Secondary]

    # Gather to Primary
    let grad2_on_primary = grad2.to(Primary)

    # Average (both on Primary now)
    let avg_grad = average_gradients(grad1, grad2_on_primary)

    # Broadcast back
    let grad_for_secondary = avg_grad.to(Secondary)
```

### Example 3: Conditional Device Selection

```simple
fn select_device(workload_size: Int) -> UserGpu:
    if workload_size < 1000:
        UserGpu::Inference
    else:
        UserGpu::Primary

fn process_adaptive(data: Tensor, size: Int) -> Tensor:
    let device = select_device(size)

    match device:
        case UserGpu::Primary:
            process_on_primary(data)
        case UserGpu::Inference:
            process_on_inference(data)

@gpu(Primary)
fn process_on_primary(data: Tensor) -> Tensor:
    ...  # Gpu[Tensor, Primary]

@gpu(Inference)
fn process_on_inference(data: Tensor) -> Tensor:
    ...  # Gpu[Tensor, Inference]
```

---

## Error Messages

### Device Mismatch

```
Error: Device mismatch at src/train.spl:42

  let y = process_on_secondary(x)
                                ^

Expected: Gpu[Int, Secondary]
Found:    Gpu[Int, Primary]

Note: Values from different devices cannot be mixed
Help: Transfer to the target device first:
      let y = process_on_secondary(x.to(Secondary))
```

### Missing GPU Annotation

```
Error: Function uses GPU values but has no @gpu annotation

  fn compute(x: Int) -> Int:
      gpu_add(x, 10)
      ^^^^^^^ GPU function called

Help: Add @gpu annotation:
      @gpu(Primary)
      fn compute(x: Int) -> Int:
          gpu_add(x, 10)
```

---

## Migration Guide

### From Old Design to New

**Old:**
```simple
enum GpuIndex: Gpu0 | Gpu1
enum UserGpu[GpuIndex]: Primary

fn compute() -> Gpu[Int, UserGpu::Primary]:
    Gpu.new(42)

let x: Gpu[Int, UserGpu::Primary] = compute()
```

**New:**
```simple
enum UserGpu: Primary

@gpu(Primary)
fn compute() -> Int:
    42

let x = compute()
```

**Steps:**
1. Remove `enum GpuIndex`
2. Simplify `enum UserGpu` (no type parameter)
3. Add `@gpu(device)` annotation to functions
4. Remove explicit `Gpu.new()` calls
5. Remove explicit type annotations (inferred!)

---

## Implementation Notes

### Type Checker Changes

```rust
// In type checker
fn check_function_return_type(fn_decl: &FunctionDecl) -> Type {
    // Check for @gpu annotation
    if let Some(device) = extract_gpu_annotation(fn_decl) {
        let declared_type = fn_decl.return_type;

        // Wrap in Gpu[T, device]
        Type::Gpu {
            inner: Box::new(declared_type),
            device: device,
        }
    } else {
        fn_decl.return_type
    }
}

fn check_gpu_function_body(
    body: &Expr,
    device: &Device,
    params: &[Param]
) -> Result<(), TypeError> {
    // Auto-unwrap parameters that are Gpu[T, device]
    let unwrapped_params = params.iter().map(|p| {
        if let Type::Gpu { inner, device: d } = &p.ty {
            if d == device {
                Param { ty: (**inner).clone(), ..p.clone() }
            } else {
                p.clone()  // Different device, keep wrapped
            }
        } else {
            p.clone()
        }
    }).collect();

    // Check body with unwrapped parameters
    check_expr(body, &unwrapped_params)?;

    Ok(())
}
```

### Codegen (Same as Before)

```rust
// MIR generation unchanged
// Gpu[T, device] still compiles to RuntimeGpuComputation
// Only difference: type system inserts wrapping automatically
```

---

## Summary

**Pattern**: `@gpu(device) fn foo() -> T` returns `Gpu[T, device]`

**Benefits:**
- ✅ Simple: One user enum, no system enum
- ✅ Inferred: Automatic type wrapping
- ✅ Safe: Compile-time device checking
- ✅ Familiar: Like async/await pattern
- ✅ Clean: Reads like normal code

**Example:**
```simple
enum UserGpu: Primary | Secondary

@gpu(Primary)
fn compute(x: Int) -> Int:
    x * 2  # Returns Gpu[Int, Primary] automatically!
```

---

**Prepared by**: Claude Code Assistant
**Date**: 2026-01-10
**Design**: Simplified GPU Types with Inference
