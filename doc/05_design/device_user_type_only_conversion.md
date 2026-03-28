# Execution Context Types - User Type Only Conversion

**Feature ID**: #194
**Status**: Designing
**Pattern**: Enum embeds custom types, implicit conversion only for user types
**Date**: 2026-01-10

---

## Critical Design Rule

**Implicit conversion is ONLY allowed for user-defined custom types, NOT primitives.**

```simple
# ❌ ERROR: Primitives cannot be implicitly converted
let x: Int = 42
let y: DeviceInt = x  # COMPILER ERROR: No implicit conversion from Int

# ✅ OK: User-defined custom types CAN be implicitly converted
let x: GpuInt = GpuInt.new(42)  # Custom type
let y: DeviceInt = x  # OK: Implicit conversion from GpuInt → DeviceInt
```

---

## Type Hierarchy

```
Primitive Types (Int, Float, Bool, String)
    ↓ (MUST wrap, NO implicit conversion)
Custom Types (GpuInt, HostInt, GpuFloat, etc.)
    ↓ (CAN implicit convert)
User Enum (DeviceInt, DeviceFloat, etc.)
    ↓ (Explicit placement)
Device Types (Gpu[UserEnum, idx], Host[UserEnum])
```

---

## Design Pattern

### Step 1: Define Custom Types

```simple
# Custom type wraps primitive - NO implicit conversion from primitive allowed
struct GpuInt:
    value: Int  # Private primitive, not directly accessible

    fn new(val: Int) -> GpuInt:
        # ONLY way to create GpuInt from Int
        GpuInt(value: val)

    fn get(self) -> Int:
        self.value

struct HostInt:
    value: Int

    fn new(val: Int) -> HostInt:
        HostInt(value: val)

    fn get(self) -> Int:
        self.value
```

### Step 2: Define User Enum

```simple
# User enum embeds ONLY custom types, never primitives
enum DeviceInt:
    Gpu(GpuInt)     # Custom type, not Int
    Host(HostInt)   # Custom type, not Int

    # No variant like: Bare(Int)  ← NEVER ALLOWED
```

### Step 3: Implicit Conversion (User Types Only)

```simple
# Implicit conversion FROM custom type TO enum
impl From[GpuInt] for DeviceInt:
    fn from(val: GpuInt) -> DeviceInt:
        DeviceInt::Gpu(val)

impl From[HostInt] for DeviceInt:
    fn from(val: HostInt) -> DeviceInt:
        DeviceInt::Host(val)

# NO implicit conversion from primitives:
# impl From[Int] for DeviceInt  ← NEVER EXISTS
```

### Step 4: Device Placement

```simple
# GpuIndex for device selection
enum GpuIndex:
    Gpu0 | Gpu1 | Gpu2 | Gpu3

# Generic device types
struct Gpu[T, const idx: GpuIndex]:
    value: T  # T must be UserEnum, not primitive

struct Host[T]:
    value: T  # T must be UserEnum, not primitive
```

---

## Enforced Type Safety

### What's Allowed ✅

```simple
# 1. Create custom type from primitive (explicit)
let x: GpuInt = GpuInt.new(42)  ✅

# 2. Implicit conversion from custom type to enum
let y: DeviceInt = x  ✅ (GpuInt → DeviceInt)

# 3. Explicit placement on device
let z: Gpu[DeviceInt, GpuIndex::Gpu0] = Gpu.new(y)  ✅
```

### What's Forbidden ❌

```simple
# 1. Bare primitive usage
let x: Int = 42
let y: DeviceInt = x  ❌ ERROR: No conversion from Int to DeviceInt

# 2. Direct primitive to enum
let x: DeviceInt = 42  ❌ ERROR: Expected DeviceInt, found Int

# 3. Primitive in device type
let x: Gpu[Int, GpuIndex::Gpu0] = Gpu.new(42)  ❌ ERROR: Expected UserEnum, found Int

# 4. Enum variant with primitive
enum DeviceInt:
    Gpu(GpuInt)
    Bare(Int)  ❌ ERROR: Enum variants must use custom types
```

---

## Complete Example

```simple
"""
Demonstrates user type only implicit conversion.
Primitives CANNOT be implicitly converted.
"""

# ============================================================================
# Custom Types (User-Defined)
# ============================================================================

struct GpuInt:
    value: Int

    fn new(val: Int) -> GpuInt:
        GpuInt(value: val)

    fn get(self) -> Int:
        self.value

struct HostInt:
    value: Int

    fn new(val: Int) -> HostInt:
        HostInt(value: val)

    fn get(self) -> Int:
        self.value

# ============================================================================
# User Enum (Embeds ONLY Custom Types)
# ============================================================================

enum DeviceInt:
    Gpu(GpuInt)     # Custom type ✅
    Host(HostInt)   # Custom type ✅
    # Bare(Int)     # Primitive ❌ NEVER ALLOWED

    fn get(self) -> Int:
        match self:
            case DeviceInt::Gpu(v): v.get()
            case DeviceInt::Host(v): v.get()

# ============================================================================
# Implicit Conversion (ONLY for Custom Types)
# ============================================================================

impl From[GpuInt] for DeviceInt:
    """Implicit conversion from GpuInt (custom type) to DeviceInt."""
    fn from(val: GpuInt) -> DeviceInt:
        DeviceInt::Gpu(val)

impl From[HostInt] for DeviceInt:
    """Implicit conversion from HostInt (custom type) to DeviceInt."""
    fn from(val: HostInt) -> DeviceInt:
        DeviceInt::Host(val)

# NO conversion from Int (primitive):
# impl From[Int] for DeviceInt  ← DOES NOT EXIST

# ============================================================================
# GpuIndex
# ============================================================================

enum GpuIndex:
    Gpu0 | Gpu1

# ============================================================================
# Device Types (Generic)
# ============================================================================

struct Gpu[T, const idx: GpuIndex]:
    value: T

    fn new(val: T) -> Gpu[T, idx]:
        Gpu(value: val)

    fn get(self) -> T:
        self.value

struct Host[T]:
    value: T

    fn new(val: T) -> Host[T]:
        Host(value: val)

    fn get(self) -> T:
        self.value

# ============================================================================
# Usage Examples
# ============================================================================

fn demonstrate_conversions():
    print("=== Type Conversion Rules ===\n")

    # ────────────────────────────────────────────────────────────────
    # ❌ ERROR CASE 1: Cannot use bare primitive
    # ────────────────────────────────────────────────────────────────
    print("❌ ERROR: Bare primitive not allowed")
    print("   let x: Int = 42")
    print("   let y: DeviceInt = x")
    print("   → No implicit conversion from Int to DeviceInt\n")

    # ────────────────────────────────────────────────────────────────
    # ✅ CORRECT: Must wrap in custom type first
    # ────────────────────────────────────────────────────────────────
    print("✅ STEP 1: Wrap primitive in custom type (explicit)")
    let x: GpuInt = GpuInt.new(42)
    print(f"   let x: GpuInt = GpuInt.new(42)")
    print(f"   → x.get() = {x.get()}\n")

    # ────────────────────────────────────────────────────────────────
    # ✅ CORRECT: Implicit conversion from custom type to enum
    # ────────────────────────────────────────────────────────────────
    print("✅ STEP 2: Implicit conversion (custom type → enum)")
    let y: DeviceInt = x  # Implicit: GpuInt → DeviceInt
    print(f"   let y: DeviceInt = x")
    print(f"   → Implicit conversion via From[GpuInt]")
    print(f"   → y.get() = {y.get()}\n")

    # ────────────────────────────────────────────────────────────────
    # ✅ CORRECT: Place enum on device
    # ────────────────────────────────────────────────────────────────
    print("✅ STEP 3: Place enum on device (explicit)")
    let z: Gpu[DeviceInt, GpuIndex::Gpu0] = Gpu.new(y)
    print(f"   let z: Gpu[DeviceInt, Gpu0] = Gpu.new(y)")
    print(f"   → z.get().get() = {z.get().get()}\n")

    # ────────────────────────────────────────────────────────────────
    # ❌ ERROR CASE 2: Cannot skip custom type wrapper
    # ────────────────────────────────────────────────────────────────
    print("❌ ERROR: Cannot skip custom type wrapper")
    print("   let z: Gpu[DeviceInt, Gpu0] = Gpu.new(DeviceInt::Gpu(42))")
    print("   → ERROR: DeviceInt::Gpu expects GpuInt, found Int\n")

    # ────────────────────────────────────────────────────────────────
    # ❌ ERROR CASE 3: Cannot put primitive in device type
    # ────────────────────────────────────────────────────────────────
    print("❌ ERROR: Cannot put primitive in device type")
    print("   let z: Gpu[Int, Gpu0] = Gpu.new(42)")
    print("   → ERROR: Type parameter T must be UserEnum, found Int\n")

fn demonstrate_correct_flow():
    print("\n=== Correct Type Flow ===\n")

    # Complete type flow: Primitive → CustomType → UserEnum → DeviceType
    print("Flow: Int → GpuInt → DeviceInt → Gpu[DeviceInt, idx]\n")

    print("Step 1: Primitive value")
    let primitive: Int = 100
    print(f"   primitive = {primitive} (type: Int)\n")

    print("Step 2: Wrap in custom type (EXPLICIT)")
    let custom: GpuInt = GpuInt.new(primitive)
    print(f"   custom = GpuInt.new({primitive})")
    print(f"   custom.get() = {custom.get()} (type: GpuInt)\n")

    print("Step 3: Convert to user enum (IMPLICIT)")
    let user_enum: DeviceInt = custom
    print(f"   user_enum = custom")
    print(f"   user_enum.get() = {user_enum.get()} (type: DeviceInt)\n")

    print("Step 4: Place on device (EXPLICIT)")
    let device_val: Gpu[DeviceInt, GpuIndex::Gpu0] = Gpu.new(user_enum)
    print(f"   device_val = Gpu.new(user_enum)")
    print(f"   device_val.get().get() = {device_val.get().get()}")
    print(f"   (type: Gpu[DeviceInt, Gpu0])\n")

    print("Summary:")
    print("  ✅ Primitive → Custom: EXPLICIT (GpuInt.new)")
    print("  ✅ Custom → Enum: IMPLICIT (From trait)")
    print("  ✅ Enum → Device: EXPLICIT (Gpu.new)")

fn demonstrate_multiple_custom_types():
    print("\n=== Multiple Custom Types ===\n")

    # Different custom types for different purposes
    struct GpuFloat:
        value: Float
        fn new(val: Float) -> GpuFloat:
            GpuFloat(value: val)
        fn get(self) -> Float:
            self.value

    struct HostFloat:
        value: Float
        fn new(val: Float) -> HostFloat:
            HostFloat(value: val)
        fn get(self) -> Float:
            self.value

    enum DeviceFloat:
        Gpu(GpuFloat)
        Host(HostFloat)

    # Each custom type has its own implicit conversion
    impl From[GpuFloat] for DeviceFloat:
        fn from(val: GpuFloat) -> DeviceFloat:
            DeviceFloat::Gpu(val)

    impl From[HostFloat] for DeviceFloat:
        fn from(val: HostFloat) -> DeviceFloat:
            DeviceFloat::Host(val)

    # Usage
    let gpu_int: GpuInt = GpuInt.new(42)
    let gpu_float: GpuFloat = GpuFloat.new(3.14)

    let int_enum: DeviceInt = gpu_int      # GpuInt → DeviceInt ✅
    let float_enum: DeviceFloat = gpu_float  # GpuFloat → DeviceFloat ✅

    # ❌ Cannot mix types:
    # let wrong: DeviceFloat = gpu_int  # ERROR: No From[GpuInt] for DeviceFloat

    print("✅ GpuInt → DeviceInt: OK")
    print("✅ GpuFloat → DeviceFloat: OK")
    print("❌ GpuInt → DeviceFloat: ERROR (type mismatch)")

# ============================================================================
# Main
# ============================================================================

fn main():
    demonstrate_conversions()
    demonstrate_correct_flow()
    demonstrate_multiple_custom_types()

    print("\n" + "=" * 60)
    print("Key Principles:")
    print("=" * 60)
    print("1. Primitives CANNOT be implicitly converted to enums")
    print("2. ONLY custom types can be implicitly converted to enums")
    print("3. Enum variants MUST use custom types, never primitives")
    print("4. Device types (Gpu/Host) accept ONLY user enums")
    print("5. This prevents ALL bare primitive leakage")
    print("=" * 60)
```

---

## Type System Rules

### Rule 1: No Primitive → Enum Conversion

```
Γ ⊢ x : Int    (primitive type)
────────────────────────────────  ERROR: No implicit conversion
Γ ⊢ x : DeviceInt
```

### Rule 2: Custom Type → Enum Conversion

```
Γ ⊢ x : GpuInt    (custom type)
impl From[GpuInt] for DeviceInt
─────────────────────────────────  OK: Implicit conversion
Γ ⊢ x : DeviceInt
```

### Rule 3: Enum Variants Must Use Custom Types

```
enum DeviceInt:
    Gpu(GpuInt)   ✅ Custom type
    Host(Int)     ❌ Primitive not allowed
```

### Rule 4: Device Types Accept Only Enums

```
Γ ⊢ v : DeviceInt    (user enum)
────────────────────────────────────  OK
Γ ⊢ Gpu.new(v) : Gpu[DeviceInt, idx]

Γ ⊢ v : Int    (primitive)
────────────────────────────────────  ERROR
Γ ⊢ Gpu.new(v) : Gpu[Int, idx]
```

---

## Compiler Implementation

### Type Checker Validation

```rust
// In type checker
fn check_enum_variant_type(variant_type: &Type) -> Result<(), TypeError> {
    match variant_type {
        Type::Named(name) if is_custom_type(name) => Ok(()),
        Type::Int | Type::Float | Type::Bool | Type::Str => {
            Err(TypeError::PrimitiveInEnumVariant {
                primitive: variant_type.clone(),
                help: "Enum variants must use custom types, not primitives. \
                       Wrap the primitive in a struct."
            })
        }
        _ => Ok(()),
    }
}

fn check_implicit_conversion(from: &Type, to: &Type) -> Result<(), TypeError> {
    // Only allow implicit conversion if From trait exists
    // AND source type is a custom type (not primitive)
    match from {
        Type::Int | Type::Float | Type::Bool | Type::Str => {
            Err(TypeError::NoImplicitConversionFromPrimitive {
                from: from.clone(),
                to: to.clone(),
                help: "Primitives cannot be implicitly converted. \
                       Wrap in a custom type first."
            })
        }
        Type::Named(custom_type) => {
            if has_from_impl(custom_type, to) {
                Ok(())
            } else {
                Err(TypeError::NoImplicitConversion {
                    from: from.clone(),
                    to: to.clone(),
                })
            }
        }
        _ => Err(TypeError::NoImplicitConversion {
            from: from.clone(),
            to: to.clone(),
        }),
    }
}
```

---

## Error Messages

### Error 1: Primitive to Enum

```
Error: Cannot implicitly convert primitive to enum

  let x: Int = 42
  let y: DeviceInt = x
          ^^^^^^^^^^ No implicit conversion from Int to DeviceInt

Primitives cannot be implicitly converted to enums.

Help: Wrap the primitive in a custom type first:
  let x: GpuInt = GpuInt.new(42)
  let y: DeviceInt = x  // Now OK (GpuInt → DeviceInt)
```

### Error 2: Primitive in Enum Variant

```
Error: Enum variant cannot use primitive type

  enum DeviceInt:
      Gpu(GpuInt)
      Bare(Int)
           ^^^ Primitive type not allowed in enum variant

Enum variants must use custom types, not primitives.

Help: Create a custom type wrapper:
  struct BareInt:
      value: Int

  enum DeviceInt:
      Gpu(GpuInt)
      Bare(BareInt)  // Now OK
```

### Error 3: Primitive in Device Type

```
Error: Device type parameter must be user enum, not primitive

  let x: Gpu[Int, GpuIndex::Gpu0] = Gpu.new(42)
             ^^^ Expected user enum, found primitive Int

Device types (Gpu, Host) only accept user-defined enums.

Help: Create custom type and enum:
  struct GpuInt:
      value: Int

  enum DeviceInt:
      Gpu(GpuInt)

  let x: Gpu[DeviceInt, GpuIndex::Gpu0] = Gpu.new(
      DeviceInt::Gpu(GpuInt.new(42))
  )
```

---

## Summary

### Key Points

1. ✅ **Enum embeds custom types** - Never primitives
2. ✅ **Implicit conversion ONLY for user types** - Not primitives
3. ✅ **Primitives must be wrapped explicitly** - Via CustomType.new()
4. ✅ **Type system enforces all rules** - Compile-time safety
5. ✅ **No primitive leakage possible** - Every step checked

### Type Flow

```
Primitive (Int, Float)
    ↓ EXPLICIT: CustomType.new(primitive)
Custom Type (GpuInt, HostInt)
    ↓ IMPLICIT: From[CustomType] for UserEnum
User Enum (DeviceInt)
    ↓ EXPLICIT: Gpu.new(enum) or Host.new(enum)
Device Type (Gpu[UserEnum, idx], Host[UserEnum])
```

### Conversion Rules

| From | To | Method | Allowed? |
|------|-----|--------|----------|
| Int | DeviceInt | Implicit | ❌ NO |
| Int | GpuInt | Explicit | ✅ YES (GpuInt.new) |
| GpuInt | DeviceInt | Implicit | ✅ YES (From trait) |
| DeviceInt | Gpu[DeviceInt, idx] | Explicit | ✅ YES (Gpu.new) |

---

**Prepared by**: Claude Code Assistant
**Date**: 2026-01-10
**Design Principle**: User Type Only Implicit Conversion
