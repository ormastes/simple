# GPU Type Inference - Implementation Plan

**Feature ID**: #194
**Pattern**: Remove system enum, add type inference like async/Future
**Date**: 2026-01-10

---

## Goals

1. **Simplify**: Remove `GpuIndex` system enum - only user enums
2. **Infer**: Automatic `Gpu[T, device]` wrapping like `async` → `Promise[T]`
3. **Verify**: Generate simple Lean 4 proofs for type safety

---

## Current Design (Complex)

```simple
# System enum (to be removed)
enum GpuIndex:
    Gpu0 | Gpu1 | Gpu2 | Gpu3

# User enum wraps system enum
enum UserGpu[GpuIndex]:
    Primary    # = GpuIndex::Gpu0
    Secondary  # = GpuIndex::Gpu1

# Explicit type
fn compute() -> Gpu[Int, UserGpu::Primary]:
    Gpu.new(42)
```

**Problems:**
- Two-level enum hierarchy (confusing)
- Explicit `Gpu[T, device]` everywhere (verbose)
- No automatic wrapping (unlike async)

---

## New Design (Simplified)

### 1. User Enum Only

```simple
# User defines enum directly (no system enum)
enum UserGpu:
    Primary
    Secondary
    Inference
    Backup
```

### 2. Type Inference (Like Async)

```simple
# Function annotation infers return type
@gpu(Primary)
fn compute() -> Int:
    42  # Returns Gpu[Int, Primary] (inferred!)

# Similar to async:
# async fn fetch() -> User:
#     ...  # Returns Promise[User] (inferred!)
```

### 3. Automatic Wrapping

```simple
@gpu(Primary)
fn add(a: Int, b: Int) -> Int:
    a + b  # Compiler wraps result in Gpu[Int, Primary]

# Call site (automatic unwrap):
let x = compute()  # Type: Gpu[Int, Primary]
let y = add(10, 20)  # Type: Gpu[Int, Primary]
let z = x + y  # GPU computation (stays on GPU)
```

---

## Implementation Phases

### Phase 1: Remove System Enum ✅ (This session)

**Goal**: Simplify to user enum only

**Changes:**
1. Remove all `GpuIndex` references
2. User enum stands alone: `enum UserGpu: Primary | Secondary | ...`
3. Direct usage: `Gpu[T, UserGpu::Primary]` (no intermediate conversion)

**Files:**
- `doc/design/simplified_gpu_enum.md` - New design doc
- `examples/simplified_gpu_demo.spl` - Working example

### Phase 2: Add Type Inference ✅ (This session)

**Goal**: Automatic `Gpu[T, device]` wrapping

**Type System Rules:**

```rust
// In type checker
fn check_gpu_function(fn_decl: &FunctionDecl) -> Type {
    // Check for @gpu annotation
    if let Some(device) = get_gpu_annotation(fn_decl) {
        let body_type = infer_type(&fn_decl.body);

        // Wrap return type in Gpu[T, device]
        Type::Gpu {
            inner: Box::new(body_type),
            device: device,
        }
    } else {
        infer_type(&fn_decl.body)
    }
}
```

**Example:**
```simple
@gpu(Primary)
fn compute() -> Int:  # Declared as Int
    42

# Actual type: Gpu[Int, Primary] (inferred!)
```

**Files:**
- `doc/design/gpu_type_inference.md` - Inference rules
- `examples/gpu_inference_demo.spl` - Inference examples

### Phase 3: Generate Lean Verification ✅ (This session)

**Goal**: Simple Lean 4 proofs for type safety

**Theorems to Prove:**

1. **Device Safety**: Functions only accept values from correct device
   ```lean
   theorem device_safety (f : GpuFunction Primary) (x : Gpu Int Primary) :
     device_of (f x) = Primary
   ```

2. **No Device Mixing**: Cannot mix values from different devices
   ```lean
   theorem no_mixing (x : Gpu Int Primary) (y : Gpu Int Secondary) :
     ¬ ∃ (z : Gpu Int ?), z = x + y
   ```

3. **Transfer Preserves Value**: Transfers don't change the value
   ```lean
   theorem transfer_value (x : Gpu Int Primary) :
     value_of x = value_of (transfer Secondary x)
   ```

4. **Inference Correctness**: Inferred type matches actual device
   ```lean
   theorem inference_correct (f : Function) (device : Device) :
     has_annotation f device →
     return_type f = Gpu (body_type f) device
   ```

**Files:**
- `verification/gpu_types/GpuTypes.lean` - Type definitions
- `verification/gpu_types/DeviceSafety.lean` - Safety proofs
- `verification/gpu_types/Inference.lean` - Inference proofs

### Phase 4: Integration Examples ✅ (This session)

**Goal**: Complete working examples

**Examples:**
1. Basic inference
2. Multi-GPU computation
3. Transfer operations
4. Neural network training
5. Error cases

**Files:**
- `examples/gpu_inference_complete.spl` - All patterns
- `doc/guide/gpu_type_inference_guide.md` - User guide

---

## Detailed Design

### Type Inference Rules

#### Rule 1: GPU Function Wrapping

```
Γ ⊢ fn has annotation @gpu(device)
Γ ⊢ body : T
────────────────────────────────────
Γ ⊢ fn : () -> Gpu[T, device]
```

#### Rule 2: Implicit Unwrap in GPU Context

```
Γ ⊢ x : Gpu[T, device]
Γ ⊢ in @gpu(device) context
────────────────────────────────────
Γ ⊢ x : T  (implicit unwrap)
```

#### Rule 3: Explicit Transfer

```
Γ ⊢ x : Gpu[T, device1]
Γ ⊢ transfer : device2
────────────────────────────────────
Γ ⊢ x.to(device2) : Gpu[T, device2]
```

#### Rule 4: Stay on Device

```
Γ ⊢ x : Gpu[Int, device]
Γ ⊢ y : Gpu[Int, device]
Γ ⊢ in @gpu(device) context
────────────────────────────────────
Γ ⊢ x + y : Gpu[Int, device]
```

### Syntax Examples

#### Before (Explicit)

```simple
enum GpuIndex: Gpu0 | Gpu1
enum UserGpu[GpuIndex]: Primary | Secondary

fn compute() -> Gpu[Int, UserGpu::Primary]:
    Gpu.new(42)

let x: Gpu[Int, UserGpu::Primary] = compute()
```

#### After (Inferred)

```simple
enum UserGpu: Primary | Secondary

@gpu(Primary)
fn compute() -> Int:
    42  # Returns Gpu[Int, Primary] automatically

let x = compute()  # Type inferred: Gpu[Int, Primary]
```

### Comparison with Async

| Async/Await | GPU Types |
|-------------|-----------|
| `async fn foo() -> T` | `@gpu(device) fn foo() -> T` |
| Returns `Promise[T]` | Returns `Gpu[T, device]` |
| `await x` unwraps | Automatic in GPU context |
| `Future.new(value)` | `Gpu.new(value)` |
| Effect inference | Device inference |

---

## Lean Verification Structure

### File Structure

```
verification/gpu_types/
├── GpuTypes.lean           # Type definitions
├── DeviceSafety.lean       # Device safety proofs
├── Inference.lean          # Type inference proofs
├── Transfer.lean           # Transfer correctness
└── lakefile.lean           # Lean project config
```

### GpuTypes.lean

```lean
-- Basic GPU type definition
inductive Device where
  | Primary : Device
  | Secondary : Device
  | Inference : Device
  | Backup : Device

-- GPU-wrapped value
structure Gpu (α : Type) (d : Device) where
  value : α
  device : Device
  device_eq : device = d

-- Type-level device tracking
def device_of {α : Type} {d : Device} (x : Gpu α d) : Device := d

-- Transfer operation
def transfer {α : Type} (d2 : Device) (x : Gpu α d1) : Gpu α d2 :=
  { value := x.value, device := d2, device_eq := rfl }
```

### DeviceSafety.lean

```lean
import GpuTypes

-- Theorem: Device is preserved in type
theorem device_type_eq {α : Type} {d : Device} (x : Gpu α d) :
  device_of x = d := by
  rfl

-- Theorem: Cannot mix devices
theorem no_device_mixing {α : Type} (x : Gpu α Primary) (y : Gpu α Secondary) :
  device_of x ≠ device_of y := by
  intro h
  cases h

-- Theorem: Transfer changes device
theorem transfer_device {α : Type} (x : Gpu α Primary) :
  device_of (transfer Secondary x) = Secondary := by
  rfl

-- Theorem: Transfer preserves value
theorem transfer_value {α : Type} (x : Gpu α Primary) :
  (transfer Secondary x).value = x.value := by
  rfl
```

### Inference.lean

```lean
import GpuTypes

-- Function with device annotation
structure GpuFunction (d : Device) (α β : Type) where
  impl : α → β
  device : Device
  device_eq : device = d

-- Inference: Function with @gpu(d) returns Gpu[T, d]
theorem inferred_return_type {d : Device} {α β : Type} (f : GpuFunction d α β) (x : α) :
  ∃ (result : Gpu β d), result.value = f.impl x := by
  exists { value := f.impl x, device := d, device_eq := rfl }
  rfl

-- Type inference is correct
theorem inference_correctness {d : Device} {α β : Type} (f : GpuFunction d α β) :
  f.device = d := by
  exact f.device_eq
```

---

## Implementation Checklist

### Phase 1: Simplification ✅
- [ ] Create `simplified_gpu_enum.md`
- [ ] Remove `GpuIndex` from examples
- [ ] User enum only design
- [ ] Basic working example

### Phase 2: Type Inference ✅
- [ ] Design inference rules
- [ ] Create `gpu_type_inference.md`
- [ ] Inference examples
- [ ] Comparison with async

### Phase 3: Lean Verification ✅
- [ ] Set up Lean project structure
- [ ] Define GPU types in Lean
- [ ] Prove device safety theorems
- [ ] Prove inference correctness
- [ ] Generate verification report

### Phase 4: Integration ✅
- [ ] Complete working examples
- [ ] User guide
- [ ] Migration guide (old → new)
- [ ] Performance notes

---

## Example: Before and After

### Before (Current Design)

```simple
enum GpuIndex: Gpu0 | Gpu1 | Gpu2 | Gpu3
enum UserGpu[GpuIndex]:
    Primary    # = GpuIndex::Gpu0
    Secondary  # = GpuIndex::Gpu1

impl From[UserGpu] for GpuIndex:
    fn from(user: UserGpu) -> GpuIndex:
        match user:
            case UserGpu::Primary: GpuIndex::Gpu0
            case UserGpu::Secondary: GpuIndex::Gpu1

fn compute(x: Gpu[Int, UserGpu::Primary]) -> Gpu[Int, UserGpu::Primary]:
    Gpu.new(x.get() + 10)

let x: Gpu[Int, UserGpu::Primary] = Gpu.new(42)
let y: Gpu[Int, UserGpu::Primary] = compute(x)
```

### After (New Design)

```simple
enum UserGpu: Primary | Secondary

@gpu(Primary)
fn compute(x: Int) -> Int:
    x + 10  # Type Gpu[Int, Primary] inferred!

let x = 42  # Type: Int (on host)
let y = compute(x)  # Type: Gpu[Int, Primary] (inferred!)
```

**Benefits:**
- ✅ No system enum boilerplate
- ✅ No explicit `Gpu.new()` calls
- ✅ No type annotations needed
- ✅ Reads like normal code
- ✅ Type safety maintained

---

## Success Criteria

1. **Simplicity**: User defines one enum, that's it
2. **Inference**: `@gpu(device)` automatically wraps return type
3. **Safety**: Lean proofs verify no device mixing
4. **Usability**: Code reads like normal functions
5. **Performance**: Zero runtime overhead

---

## Timeline

- **Phase 1**: 1 hour (simplification)
- **Phase 2**: 1 hour (inference rules)
- **Phase 3**: 1 hour (Lean verification)
- **Phase 4**: 30 minutes (integration)

**Total**: ~3.5 hours

---

**Prepared by**: Claude Code Assistant
**Date**: 2026-01-10
**Status**: Ready to implement
