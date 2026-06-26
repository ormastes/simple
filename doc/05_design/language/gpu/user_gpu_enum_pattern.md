# User GPU Enum Pattern - Semantic Device Names

**Feature ID**: #194
**Pattern**: User enum wrapping GpuIndex with implicit conversion
**Date**: 2026-01-10

---

## Pattern Overview

Define a **user enum** that wraps the underlying `GpuIndex` type, providing semantic names that implicitly convert to numeric indices.

```simple
# Base enum (system-defined)
enum GpuIndex:
    Gpu0 | Gpu1 | Gpu2 | Gpu3

# User enum (application-defined, wraps GpuIndex)
enum UserGpu[GpuIndex]:
    Primary    # = GpuIndex::Gpu0
    Secondary  # = GpuIndex::Gpu1
    Inference  # = GpuIndex::Gpu2
    Backup     # = GpuIndex::Gpu3

# All equivalent:
Gpu[Int, GpuIndex::Gpu0]      # Explicit index
Gpu[Int, UserGpu::Primary]    # Semantic name
Gpu[Int, 0_gpu]               # Literal syntax
```

**Key Insight**: The user enum provides **semantic meaning** while maintaining **type compatibility** with the underlying index.

---

## Design Principles

### 1. Enum with Type Parameter

```simple
enum UserGpu[GpuIndex]:
    """
    User-defined enum that wraps GpuIndex.
    Each variant maps to a specific GpuIndex value.
    """
    Primary    # GpuIndex::Gpu0 (high-performance)
    Secondary  # GpuIndex::Gpu1 (memory-optimized)
    Inference  # GpuIndex::Gpu2 (inference-specialized)
    Backup     # GpuIndex::Gpu3 (fallback device)
```

### 2. Implicit Conversion

```simple
# UserGpu::Primary implicitly converts to GpuIndex::Gpu0
impl From[UserGpu] for GpuIndex:
    fn from(user: UserGpu) -> GpuIndex:
        match user:
            case UserGpu::Primary:   GpuIndex::Gpu0
            case UserGpu::Secondary: GpuIndex::Gpu1
            case UserGpu::Inference: GpuIndex::Gpu2
            case UserGpu::Backup:    GpuIndex::Gpu3

# This makes all these equivalent:
let x: Gpu[Int, UserGpu::Primary]    # User enum
let y: Gpu[Int, GpuIndex::Gpu0]      # System enum (implicit conversion)
# x and y have the SAME type after conversion
```

### 3. Literal Syntax

```simple
# Numeric literals with _gpu suffix
0_gpu  →  GpuIndex::Gpu0  →  UserGpu::Primary
1_gpu  →  GpuIndex::Gpu1  →  UserGpu::Secondary
2_gpu  →  GpuIndex::Gpu2  →  UserGpu::Inference
3_gpu  →  GpuIndex::Gpu3  →  UserGpu::Backup

# Usage
let x: Gpu[Int, 0_gpu]  # Literal
let y: Gpu[Int, UserGpu::Primary]  # Semantic
# Both create the same type
```

---

## Complete Example 1: Basic Pattern

```simple
"""
Demonstrates user enum wrapping GpuIndex with semantic names.
"""

# ============================================================================
# Base System Enum
# ============================================================================

enum GpuIndex:
    """System-level GPU indices (0-3)."""
    Gpu0
    Gpu1
    Gpu2
    Gpu3

    fn to_int(self) -> Int:
        match self:
            case GpuIndex::Gpu0: 0
            case GpuIndex::Gpu1: 1
            case GpuIndex::Gpu2: 2
            case GpuIndex::Gpu3: 3

# ============================================================================
# User-Defined Enum (Wraps GpuIndex)
# ============================================================================

enum UserGpu[GpuIndex]:
    """
    Application-specific GPU roles.
    Wraps GpuIndex with semantic names.
    """
    Primary    # High-performance compute (Gpu0)
    Secondary  # Memory-optimized (Gpu1)
    Inference  # Inference-specialized (Gpu2)
    Backup     # Fallback device (Gpu3)

    fn description(self) -> String:
        """Get semantic description."""
        match self:
            case UserGpu::Primary:
                "Primary (high-performance compute)"
            case UserGpu::Secondary:
                "Secondary (memory-optimized)"
            case UserGpu::Inference:
                "Inference (specialized for inference)"
            case UserGpu::Backup:
                "Backup (fallback device)"

# ============================================================================
# Implicit Conversion (UserGpu → GpuIndex)
# ============================================================================

impl From[UserGpu] for GpuIndex:
    """Implicit conversion from user enum to system enum."""
    fn from(user: UserGpu) -> GpuIndex:
        match user:
            case UserGpu::Primary:   GpuIndex::Gpu0
            case UserGpu::Secondary: GpuIndex::Gpu1
            case UserGpu::Inference: GpuIndex::Gpu2
            case UserGpu::Backup:    GpuIndex::Gpu3

# Reverse conversion (explicit)
impl From[GpuIndex] for UserGpu:
    """Explicit conversion from system enum to user enum."""
    fn from(idx: GpuIndex) -> UserGpu:
        match idx:
            case GpuIndex::Gpu0: UserGpu::Primary
            case GpuIndex::Gpu1: UserGpu::Secondary
            case GpuIndex::Gpu2: UserGpu::Inference
            case GpuIndex::Gpu3: UserGpu::Backup

# ============================================================================
# Generic Device Type
# ============================================================================

struct Gpu[T, const idx: GpuIndex]:
    """
    Generic GPU computation.
    Accepts GpuIndex (which UserGpu converts to).
    """
    value: T
    device: GpuIndex

    fn new(val: T) -> Gpu[T, idx]:
        Gpu(value: val, device: idx)

# ============================================================================
# Usage: All Equivalent Forms
# ============================================================================

fn example_equivalence():
    print("=== Equivalent Type Forms ===\n")

    let data: Int = 42

    # Form 1: System enum (explicit)
    let gpu1: Gpu[Int, GpuIndex::Gpu0] = Gpu.new(data)
    print("Form 1: Gpu[Int, GpuIndex::Gpu0]")

    # Form 2: User enum (semantic)
    let gpu2: Gpu[Int, UserGpu::Primary] = Gpu.new(data)
    print("Form 2: Gpu[Int, UserGpu::Primary]")
    # UserGpu::Primary implicitly converts to GpuIndex::Gpu0

    # Form 3: Literal (concise)
    let gpu3: Gpu[Int, 0_gpu] = Gpu.new(data)
    print("Form 3: Gpu[Int, 0_gpu]")

    print("\n✅ All three forms create the SAME type!")
    print("   Type: Gpu[Int, GpuIndex::Gpu0]\n")
```

---

## Example 2: Semantic Device Selection

```simple
"""
Using semantic names for clearer code intent.
"""

# Custom data type
struct Tensor:
    data: List[Float]
    shape: List[Int]

    fn new(data: List[Float], shape: List[Int]) -> Tensor:
        Tensor(data: data, shape: shape)

# ============================================================================
# Application-Specific Workflow
# ============================================================================

fn train_model(data: Tensor) -> Tensor:
    """Training uses Primary GPU (high-performance)."""
    print("Training on Primary GPU...")

    # Use semantic name for clarity
    let gpu_data: Gpu[Tensor, UserGpu::Primary] = Gpu.new(data)

    # Training computation...
    print("  Using high-performance compute")
    gpu_data.value

fn run_inference(data: Tensor) -> Tensor:
    """Inference uses Inference GPU (specialized)."""
    print("Inference on Inference GPU...")

    # Semantic name shows intent
    let gpu_data: Gpu[Tensor, UserGpu::Inference] = Gpu.new(data)

    # Inference computation...
    print("  Using inference-optimized kernels")
    gpu_data.value

fn backup_computation(data: Tensor) -> Tensor:
    """Backup uses Backup GPU (fallback)."""
    print("Backup on Backup GPU...")

    let gpu_data: Gpu[Tensor, UserGpu::Backup] = Gpu.new(data)

    print("  Using fallback device")
    gpu_data.value

fn example_semantic_workflow():
    print("\n=== Example 2: Semantic Workflow ===\n")

    let tensor = Tensor.new([1.0, 2.0, 3.0], [3])

    train_model(tensor)
    run_inference(tensor)
    backup_computation(tensor)

    print("\n✅ Code clearly shows which GPU for what purpose!")
```

**Output:**
```
=== Example 2: Semantic Workflow ===

Training on Primary GPU...
  Using high-performance compute
Inference on Inference GPU...
  Using inference-optimized kernels
Backup on Backup GPU...
  Using fallback device

✅ Code clearly shows which GPU for what purpose!
```

---

## Example 3: Mixed Numeric and Semantic

```simple
"""
Mixing literal indices and semantic names in same codebase.
All interoperate seamlessly.
"""

fn process_with_literal(data: Tensor) -> Gpu[Tensor, 0_gpu]:
    """Function using literal index."""
    print("Processing with literal: 0_gpu")
    Gpu.new(data)

fn process_with_semantic(data: Tensor) -> Gpu[Tensor, UserGpu::Primary]:
    """Function using semantic name."""
    print("Processing with semantic: UserGpu::Primary")
    Gpu.new(data)

fn process_with_system(data: Tensor) -> Gpu[Tensor, GpuIndex::Gpu0]:
    """Function using system enum."""
    print("Processing with system: GpuIndex::Gpu0")
    Gpu.new(data)

fn example_mixed_usage():
    print("\n=== Example 3: Mixed Usage ===\n")

    let tensor = Tensor.new([1.0, 2.0], [2])

    # All return the SAME type
    let result1 = process_with_literal(tensor)
    let result2 = process_with_semantic(tensor)
    let result3 = process_with_system(tensor)

    # Can assign to each other
    let x: Gpu[Tensor, 0_gpu] = result2  # Semantic → Literal
    let y: Gpu[Tensor, UserGpu::Primary] = result1  # Literal → Semantic
    let z: Gpu[Tensor, GpuIndex::Gpu0] = result2  # Semantic → System

    print("\n✅ All forms are type-compatible!")
    print("   Can freely convert between literal/semantic/system")
```

---

## Example 4: Configuration-Based Selection

```simple
"""
Runtime configuration selects user enum, used at compile time.
"""

struct AppConfig:
    """Application configuration."""
    training_gpu: UserGpu
    inference_gpu: UserGpu
    backup_gpu: UserGpu

    fn default() -> AppConfig:
        AppConfig(
            training_gpu: UserGpu::Primary,
            inference_gpu: UserGpu::Inference,
            backup_gpu: UserGpu::Backup
        )

    fn alternative() -> AppConfig:
        """Alternative configuration (all on Primary)."""
        AppConfig(
            training_gpu: UserGpu::Primary,
            inference_gpu: UserGpu::Primary,  # Use Primary for inference too
            backup_gpu: UserGpu::Secondary    # Secondary as backup
        )

fn example_config_based():
    print("\n=== Example 4: Configuration-Based ===\n")

    let config = AppConfig.default()

    print("Default configuration:")
    print(f"  Training: {config.training_gpu.description()}")
    print(f"  Inference: {config.inference_gpu.description()}")
    print(f"  Backup: {config.backup_gpu.description()}\n")

    let alt_config = AppConfig.alternative()

    print("Alternative configuration:")
    print(f"  Training: {alt_config.training_gpu.description()}")
    print(f"  Inference: {alt_config.inference_gpu.description()}")
    print(f"  Backup: {alt_config.backup_gpu.description()}")

    print("\n✅ User enum provides flexible, readable configuration!")
```

**Output:**
```
=== Example 4: Configuration-Based ===

Default configuration:
  Training: Primary (high-performance compute)
  Inference: Inference (specialized for inference)
  Backup: Backup (fallback device)

Alternative configuration:
  Training: Primary (high-performance compute)
  Inference: Primary (high-performance compute)
  Backup: Secondary (memory-optimized)

✅ User enum provides flexible, readable configuration!
```

---

## Example 5: Type Safety with Semantic Names

```simple
"""
Type system enforces correct device usage via semantic names.
"""

fn train_on_primary(model: Gpu[Model, UserGpu::Primary]) -> Gpu[Model, UserGpu::Primary]:
    """Training MUST use Primary GPU."""
    print("Training on Primary (verified at compile time)")
    model

fn infer_on_inference(model: Gpu[Model, UserGpu::Inference]) -> Gpu[Tensor, UserGpu::Inference]:
    """Inference MUST use Inference GPU."""
    print("Inference on Inference device (verified at compile time)")
    Gpu.new(Tensor.new([], []))

fn example_type_safety():
    print("\n=== Example 5: Type Safety ===\n")

    let model_data = Model.new()

    # Place on Primary
    let primary_model: Gpu[Model, UserGpu::Primary] = Gpu.new(model_data)

    # OK: matches function signature
    let trained = train_on_primary(primary_model)
    print("✅ train_on_primary(primary_model) - OK\n")

    # Place on Inference
    let inference_model: Gpu[Model, UserGpu::Inference] = Gpu.new(model_data)

    # OK: matches function signature
    let output = infer_on_inference(inference_model)
    print("✅ infer_on_inference(inference_model) - OK\n")

    # ❌ Type error: wrong GPU
    # train_on_primary(inference_model)  # ERROR!
    print("❌ train_on_primary(inference_model) - TYPE ERROR")
    print("   Expected: Gpu[Model, UserGpu::Primary]")
    print("   Found:    Gpu[Model, UserGpu::Inference]")

struct Model:
    fn new() -> Model:
        Model()
```

---

## Example 6: Implicit Conversion in Action

```simple
"""
Demonstrates implicit conversion from UserGpu to GpuIndex.
"""

fn transfer_to_system[T](
    user_gpu: Gpu[T, UserGpu::Primary]
) -> Gpu[T, GpuIndex::Gpu0]:
    """
    Accepts UserGpu::Primary, returns GpuIndex::Gpu0.
    They're the same type after implicit conversion.
    """
    print("Implicit conversion: UserGpu::Primary → GpuIndex::Gpu0")
    user_gpu  # No explicit conversion needed!

fn transfer_to_user[T](
    system_gpu: Gpu[T, GpuIndex::Gpu0]
) -> Gpu[T, UserGpu::Primary]:
    """
    Accepts GpuIndex::Gpu0, returns UserGpu::Primary.
    Implicit conversion in reverse.
    """
    print("Implicit conversion: GpuIndex::Gpu0 → UserGpu::Primary")
    system_gpu  # No explicit conversion needed!

fn example_implicit_conversion():
    print("\n=== Example 6: Implicit Conversion ===\n")

    let data: Int = 100

    # Create with user enum
    let user: Gpu[Int, UserGpu::Primary] = Gpu.new(data)
    print("Created: Gpu[Int, UserGpu::Primary]")

    # Convert to system enum (implicit)
    let system: Gpu[Int, GpuIndex::Gpu0] = transfer_to_system(user)
    print("After conversion: Gpu[Int, GpuIndex::Gpu0]\n")

    # Convert back to user enum (implicit)
    let back: Gpu[Int, UserGpu::Primary] = transfer_to_user(system)
    print("After reverse: Gpu[Int, UserGpu::Primary]\n")

    print("✅ No explicit .into() or .from() needed!")
    print("   Compiler handles conversion automatically")
```

---

## Example 7: Multiple User Enums

```simple
"""
Multiple applications can define their own user enums.
All convert to the same underlying GpuIndex.
"""

# Application 1: ML training
enum MLGpu[GpuIndex]:
    Trainer    # = Gpu0
    Validator  # = Gpu1
    Tester     # = Gpu2

impl From[MLGpu] for GpuIndex:
    fn from(ml: MLGpu) -> GpuIndex:
        match ml:
            case MLGpu::Trainer:   GpuIndex::Gpu0
            case MLGpu::Validator: GpuIndex::Gpu1
            case MLGpu::Tester:    GpuIndex::Gpu2

# Application 2: Rendering
enum RenderGpu[GpuIndex]:
    Display    # = Gpu0
    Compute    # = Gpu1
    Capture    # = Gpu2

impl From[RenderGpu] for GpuIndex:
    fn from(render: RenderGpu) -> GpuIndex:
        match render:
            case RenderGpu::Display: GpuIndex::Gpu0
            case RenderGpu::Compute: GpuIndex::Gpu1
            case RenderGpu::Capture: GpuIndex::Gpu2

fn example_multiple_user_enums():
    print("\n=== Example 7: Multiple User Enums ===\n")

    let data: Int = 42

    # ML application uses MLGpu
    let ml_gpu: Gpu[Int, MLGpu::Trainer] = Gpu.new(data)
    print("ML application: Gpu[Int, MLGpu::Trainer]")

    # Rendering application uses RenderGpu
    let render_gpu: Gpu[Int, RenderGpu::Display] = Gpu.new(data)
    print("Render application: Gpu[Int, RenderGpu::Display]")

    # Both map to GpuIndex::Gpu0, so they're compatible!
    let system1: Gpu[Int, GpuIndex::Gpu0] = ml_gpu
    let system2: Gpu[Int, GpuIndex::Gpu0] = render_gpu

    print("\nBoth convert to: Gpu[Int, GpuIndex::Gpu0]")
    print("✅ Multiple user enums can coexist!")
    print("   All map to same underlying system enum")
```

---

## Syntax Summary

### Enum Definition

```simple
enum UserGpu[GpuIndex]:
    #        ^^^^^^^^^^^ - Type parameter (wraps this type)
    Primary    # First variant
    Secondary  # Second variant
    ...
```

### Implicit Conversion

```simple
impl From[UserGpu] for GpuIndex:
    fn from(user: UserGpu) -> GpuIndex:
        match user:
            case UserGpu::Primary: GpuIndex::Gpu0
            ...
```

### Usage

```simple
# All equivalent after conversion:
Gpu[T, UserGpu::Primary]    # User enum
Gpu[T, GpuIndex::Gpu0]      # System enum
Gpu[T, 0_gpu]               # Literal
```

---

## Type System Rules

### Rule 1: User Enum → System Enum (Implicit)

```
Γ ⊢ x : UserGpu::Primary
impl From[UserGpu] for GpuIndex
─────────────────────────────────
Γ ⊢ x : GpuIndex::Gpu0  (implicit)
```

### Rule 2: Type Equivalence

```
UserGpu::Primary  ≡  GpuIndex::Gpu0  (via From impl)
∴ Gpu[T, UserGpu::Primary]  ≡  Gpu[T, GpuIndex::Gpu0]
```

### Rule 3: Literal Conversion

```
0_gpu  →  GpuIndex::Gpu0  (literal syntax)
GpuIndex::Gpu0  ←  UserGpu::Primary  (via From impl)
∴ 0_gpu  ≡  UserGpu::Primary
```

---

## Benefits

### 1. Semantic Clarity
```simple
# Before (numeric indices)
Gpu[Model, GpuIndex::Gpu0]  # What's Gpu0 for?

# After (semantic names)
Gpu[Model, UserGpu::Primary]  # Clear: primary training device
```

### 2. Configuration Flexibility
```simple
# Easy to change GPU assignments
enum UserGpu[GpuIndex]:
    Primary: GpuIndex::Gpu1  # Change from Gpu0 to Gpu1
    # Only change here, all code still works!
```

### 3. Multiple Domains
```simple
# Different apps define their own semantic names
enum MLGpu[GpuIndex]: Trainer | Validator | Tester
enum RenderGpu[GpuIndex]: Display | Compute | Capture
# Both map to same underlying GpuIndex
```

### 4. Type Safety
```simple
# Compiler enforces semantic GPU usage
fn train(model: Gpu[Model, UserGpu::Primary])  # Must be Primary
fn infer(model: Gpu[Model, UserGpu::Inference]) # Must be Inference
```

---

## Implementation Notes

### Compiler Support

The compiler must:
1. **Parse `enum Name[Type]:`** syntax
2. **Track implicit `From` conversions** for type checking
3. **Resolve type equivalence** through conversion chains
4. **Support literal suffix** `0_gpu` → `GpuIndex::Gpu0`

### Type Checking

```rust
// In type checker
fn check_type_equivalence(t1: &Type, t2: &Type) -> bool {
    if t1 == t2 {
        return true;
    }

    // Check if t1 can implicitly convert to t2
    if has_from_impl(t1, t2) {
        return true;
    }

    // Check generic type parameters
    match (t1, t2) {
        (Type::Generic { name: n1, args: a1 },
         Type::Generic { name: n2, args: a2 }) => {
            n1 == n2 && check_args_equivalence(a1, a2)
        }
        _ => false
    }
}
```

---

## Summary

**Pattern**: User enum wraps system enum with semantic names + implicit conversion

**Syntax**:
```simple
enum UserGpu[GpuIndex]:  # Wraps GpuIndex
    Primary              # Maps to Gpu0
```

**Equivalence**:
```simple
Gpu[T, UserGpu::Primary] ≡ Gpu[T, GpuIndex::Gpu0] ≡ Gpu[T, 0_gpu]
```

**Benefits**:
- ✅ Semantic clarity in code
- ✅ Flexible configuration
- ✅ Type safety maintained
- ✅ Multiple user enums supported
- ✅ Implicit conversion (no boilerplate)

---

**Prepared by**: Claude Code Assistant
**Date**: 2026-01-10
**Pattern**: User Enum with Implicit Conversion to System Type
