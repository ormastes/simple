# Newtype Design Patterns for Simple Language
**Version**: 1.0
**Date**: 2026-01-20
**Related**: Primitive API Migration (doc/report/primitive_api_migration_complete_2026-01-20.md)

---

## Purpose

This guide establishes when to use newtype wrappers (via `unit` keyword) versus bare primitives in Simple's public APIs, based on lessons learned from the primitive API migration project.

---

## Core Principle

**Use newtypes for domain semantics, not to wrap all primitives.**

Type safety comes from preventing confusion between similar-looking values with different meanings (Metallic vs Roughness), not from eliminating primitives entirely.

---

## Decision Framework

### When to Create a Newtype

✅ **Create a newtype when**:

1. **Semantic distinction prevents bugs**
   ```simple
   # Good: Prevents parameter swap bugs
   unit Metallic: f32 as metallic
   unit Roughness: f32 as roughness

   fn set_material(metallic: Metallic, roughness: Roughness)
   # Compiler prevents: set_material(roughness, metallic)
   ```

2. **Values have physical meaning or units**
   ```simple
   # Good: Encode physical units
   unit Milliseconds: u64 as ms
   unit ByteCount: u64 as bytes
   unit Intensity: f32 as intensity  # lumens/watts
   ```

3. **Finite set of named modes** (use enum instead)
   ```simple
   # Good: Named options better than magic numbers
   pub enum ShutdownMode:
       Read
       Write
       Both

   # Instead of: fn shutdown(mode: i32)  // 0=read, 1=write, 2=both
   ```

4. **Helper methods add domain operations**
   ```simple
   # Good: Domain-specific operations
   impl Metallic:
       pub fn is_metal() -> bool:
           return self.value() >= 0.9

       pub fn is_dielectric() -> bool:
           return self.value() <= 0.1
   ```

5. **Type prevents mixing incompatible concepts**
   ```simple
   # Good: Cannot mix vertex/light indices
   unit VertexIndex: i32 as vtx_idx
   unit LightIndex: i32 as light_idx
   ```

### When to Keep Primitives

❌ **DO NOT wrap primitives when**:

1. **Specification requires primitives**
   ```simple
   # Correct: JSON spec mandates these types
   pub enum JsonValue:
       bool(bool)        # JSON boolean
       Number(f64)       # JSON number (f64 per spec)
       Integer(i64)      # Extension
   ```

2. **Generic mathematical operations**
   ```simple
   # Correct: Math functions operate on raw numbers
   pub fn lerp(a: f32, b: f32, t: f32) -> f32
   pub fn sin(x: f32) -> f32
   pub fn random() -> f32  # [0.0, 1.0)
   ```

3. **Universal predicate patterns**
   ```simple
   # Correct: Boolean predicates are standard
   pub fn is_empty() -> bool
   pub fn has_field(name: text) -> bool
   pub fn is_valid() -> bool
   ```

4. **FFI boundaries with mixed semantics**
   ```simple
   # Correct: Cannot wrap when same type means different things
   extern fn rt_file_open(path: text, mode: i32) -> i32
   # Returns: positive=file descriptor, negative=error code
   ```

5. **Industry-standard APIs**
   ```simple
   # Correct: Matches Rust std::io::SeekFrom, POSIX lseek
   pub enum SeekFrom:
       Start(u64)      # Unsigned: absolute position
       End(i64)        # Signed: offset from end
       Current(i64)    # Signed: relative offset
   ```

6. **Generic collection operations**
   ```simple
   # Correct: Array indexing is inherently primitive
   pub fn get(index: i64) -> T
   pub fn len() -> i64
   ```

---

## Naming Conventions

### Unit Type Names

**Pattern**: Descriptive noun or adjective describing the semantic concept

✅ **Good**:
```simple
unit Metallic: f32 as metallic          # Adjective describing property
unit Roughness: f32 as roughness        # Noun for surface property
unit ByteCount: u64 as bytes            # Noun with unit clarification
unit Milliseconds: u64 as ms            # Explicit time unit
unit VertexIndex: i32 as vtx_idx        # Semantic index type
```

❌ **Bad**:
```simple
unit F32: f32 as f32_val                # Too generic, no semantics
unit Value: f32 as val                  # Meaningless wrapper
unit Number: i32 as num                 # No domain meaning
```

### Suffix Conventions

**Pattern**: Use conventional suffixes for clarity

| Suffix | Meaning | Example |
|--------|---------|---------|
| `Count` | Number of items | `ByteCount`, `TokenCount` |
| `Index` | Position in collection | `VertexIndex`, `LightIndex` |
| `Size` | Dimension or capacity | `TextureSize`, `BufferSize` |
| `Id` | Unique identifier | `SessionId`, `StateId` |
| `Mode` | Operational mode | `FileMode` (use enum instead) |
| Time units | Duration measure | `Milliseconds`, `Seconds` |

### Enum Names for Modes

**Pattern**: Singular noun describing the category

✅ **Good**:
```simple
pub enum ShutdownMode:     # Category of shutdown operations
    Read
    Write
    Both

pub enum OpenMode:         # Category of file open operations
    Read
    Write
    ReadWrite
    Append
```

❌ **Bad**:
```simple
pub enum ShutdownModes     # Plural - incorrect
pub enum ShutdownType      # "Type" suffix unnecessary
```

---

## Implementation Patterns

### Pattern 1: Basic Unit with Helpers

```simple
# Material metallic coefficient (0.0 = dielectric, 1.0 = metal)
unit Metallic: f32 as metallic

impl Metallic:
    pub fn from_f32(n: f32) -> Metallic:
        """Create metallic value, clamped to [0.0, 1.0]."""
        val clamped = max(0.0, min(1.0, n))
        return clamped_metallic

    pub fn value() -> f32:
        """Get underlying f32 value."""
        return self as f32

    pub fn is_metal() -> bool:
        """Check if value indicates metallic surface (>= 0.9)."""
        return self.value() >= 0.9

    pub fn is_dielectric() -> bool:
        """Check if value indicates dielectric surface (<= 0.1)."""
        return self.value() <= 0.1

    # Factory methods for common values
    pub fn metal() -> Metallic:
        return 1.0_metallic

    pub fn dielectric() -> Metallic:
        return 0.0_metallic
```

**When to use**: Simple domain values with validation and common checks.

### Pattern 2: Enum for Finite Modes

```simple
# TCP/UDP shutdown modes
pub enum ShutdownMode:
    Read       # Shutdown read operations
    Write      # Shutdown write operations
    Both       # Shutdown both read and write

impl ShutdownMode:
    pub fn to_i64() -> i64:
        """Convert to integer for FFI (0=read, 1=write, 2=both)."""
        match self:
            case Read: 0
            case Write: 1
            case Both: 2

    pub fn to_string() -> text:
        match self:
            case Read: "read"
            case Write: "write"
            case Both: "both"

    pub fn is_read() -> bool:
        """Check if mode shuts down reading."""
        match self:
            case Read: true
            case Both: true
            case _: false
```

**When to use**: Finite set of named options (replaces magic numbers).

### Pattern 3: Count/Index with Validation

```simple
# Generic count (signed, can represent differences)
unit Count: i64 as count

impl Count:
    pub fn from_i64(n: i64) -> Count:
        return n_count

    pub fn value() -> i64:
        return self as i64

    pub fn zero() -> Count:
        return 0_count

    pub fn is_zero() -> bool:
        return self.value() == 0

    pub fn increment() -> Count:
        return (self.value() + 1)_count

    pub fn add(other: Count) -> Count:
        return (self.value() + other.value())_count
```

**When to use**: Counts, indices, or IDs that benefit from arithmetic operations.

### Pattern 4: Physical Units with Conversions

```simple
unit Milliseconds: u64 as ms

impl Milliseconds:
    pub fn from_u64(n: u64) -> Milliseconds:
        return n_ms

    pub fn value() -> u64:
        return self as u64

    pub fn to_seconds() -> Seconds:
        return (self.value() / 1000)_s

    pub fn seconds(n: u64) -> Milliseconds:
        """Create from seconds."""
        return (n * 1000)_ms

    pub fn minutes(n: u64) -> Milliseconds:
        """Create from minutes."""
        return (n * 60 * 1000)_ms
```

**When to use**: Physical quantities with unit conversions.

---

## Anti-Patterns

### ❌ Anti-Pattern 1: Generic Wrappers

```simple
# BAD: No semantic value
unit F32: f32 as f32_val
unit I32: i32 as i32_val
unit Bool: bool as bool_val

fn calculate(a: F32, b: F32) -> F32  # What are a and b?
```

**Why bad**: Provides no semantic information, just noise.

**Fix**: Use descriptive domain-specific types or keep as primitives.

### ❌ Anti-Pattern 2: Wrapping Spec-Mandated Types

```simple
# BAD: Breaks JSON spec compliance
unit JsonBool: bool as json_bool
unit JsonNumber: f64 as json_num

pub enum JsonValue:
    bool(JsonBool)     # Should be bare bool
    Number(JsonNumber) # Should be bare f64
```

**Why bad**: External specifications (JSON, HTTP, etc.) mandate primitive types for interoperability.

**Fix**: Keep spec-mandated types as primitives.

### ❌ Anti-Pattern 3: Wrapping Math Functions

```simple
# BAD: No domain semantics
unit Coefficient: f32 as coef

fn lerp(a: Coefficient, b: Coefficient, t: Coefficient) -> Coefficient
```

**Why bad**: Generic math operations don't have semantic constraints. `lerp` works on any numbers.

**Fix**: Keep generic math functions with primitive parameters.

### ❌ Anti-Pattern 4: Predicate Wrappers

```simple
# BAD: Boolean predicates don't need wrapping
unit IsEmpty: bool as is_empty_val

fn is_empty() -> IsEmpty  # Confusing, adds no value
```

**Why bad**: Boolean predicates are a universal pattern that doesn't need domain types.

**Fix**: Return bare `bool` for predicates.

---

## Module Organization

### File Structure

```
simple/std_lib/src/units/
├── __init__.spl          # Exports all unit modules
├── core.spl              # Generic types (Count, Index, Hash)
├── graphics.spl          # Graphics domain types
├── net.spl               # Networking types
├── time.spl              # Time and duration types
├── size.spl              # Size and capacity types
├── file.spl              # File system types
├── lms.spl               # Language model system types
└── ids.spl               # Identifier types
```

### Module Responsibilities

| Module | Responsibility | Examples |
|--------|----------------|----------|
| `core` | Generic cross-domain types | Count, Index, Hash, ErrorCode |
| `graphics` | Rendering and materials | Metallic, Roughness, Intensity |
| `net` | Networking operations | BufferSize, PacketSize, ShutdownMode |
| `time` | Time and duration | Milliseconds, Seconds, Duration |
| `size` | Sizes and capacities | ByteCount, FileSize |
| `lms` | LLM interactions | TokenCount, SessionId, Temperature |

**Guideline**: Create new module when domain has >5 related types.

---

## Migration Guide

### Adding a New Unit Type

**Steps**:

1. **Identify semantic need**
   - Does confusion between similar values cause bugs?
   - Do helper methods add domain value?

2. **Choose appropriate module**
   ```simple
   # For domain-specific type, add to relevant module
   # simple/std_lib/src/units/graphics.spl

   # For generic type, add to core
   # simple/std_lib/src/units/core.spl
   ```

3. **Define unit with documentation**
   ```simple
   # Surface roughness coefficient (0.0 = smooth, 1.0 = rough)
   unit Roughness: f32 as roughness
   ```

4. **Implement methods**
   ```simple
   impl Roughness:
       pub fn from_f32(n: f32) -> Roughness:
           """Create roughness, clamped to [0.0, 1.0]."""
           val clamped = max(0.0, min(1.0, n))
           return clamped_roughness

       pub fn value() -> f32:
           return self as f32

       # Add domain-specific helpers
       pub fn is_smooth() -> bool:
           return self.value() < 0.2
   ```

5. **Update call sites**
   ```simple
   # Before:
   pub struct PbrMaterial:
       roughness: f32

   # After:
   pub struct PbrMaterial:
       roughness: Roughness
   ```

6. **Verify no regressions**
   ```bash
   make check
   ```

### Converting Enum from Magic Numbers

**Example**: Converting file modes from i32 to enum

**Before**:
```simple
extern fn rt_file_open(path: text, mode: i32) -> i32
# Callers use: rt_file_open("file.txt", 0)  // What is 0?
```

**After**:
```simple
# Create enum
pub enum FileMode:
    ReadOnly     # 0
    ReadWrite    # 1
    WriteOnly    # 2

impl FileMode:
    pub fn to_i32() -> i32:
        match self:
            case ReadOnly: 0
            case ReadWrite: 1
            case WriteOnly: 2

# Update FFI wrapper
pub fn file_open(path: text, mode: FileMode) -> Result<i32>:
    val mode_int = mode.to_i32()
    return rt_file_open(path, mode_int)

# Callers now: file_open("file.txt", FileMode::ReadOnly)
```

---

## Checklist for New Types

Before creating a newtype, verify:

- [ ] Type represents a domain-specific concept (not just wrapping a primitive)
- [ ] Confusion between similar values causes actual bugs
- [ ] Helper methods provide domain value (not just getters)
- [ ] Type doesn't break specification compliance (JSON, HTTP, etc.)
- [ ] Type doesn't wrap generic math operations (lerp, sin, etc.)
- [ ] Name follows conventions (descriptive noun/adjective + suffix)
- [ ] Documentation explains semantic meaning and valid ranges
- [ ] Tests verify type safety and helper methods

---

## Examples from Simple Stdlib

### ✅ Good Uses of Newtypes

1. **PBR Material Properties** (units/graphics.spl)
   ```simple
   unit Metallic: f32 as metallic
   unit Roughness: f32 as roughness
   # Prevents: set_material(roughness, metallic)
   ```

2. **Network Shutdown** (units/net.spl)
   ```simple
   pub enum ShutdownMode:
       Read
       Write
       Both
   # Replaces magic numbers: shutdown(2) → shutdown(ShutdownMode::Both)
   ```

3. **Token Counting** (units/lms.spl)
   ```simple
   unit TokenCount: u64 as tokens

   impl TokenCount:
       pub fn limit_claude() -> TokenCount:
           return 100000_tokens

       pub fn exceeds(limit: TokenCount) -> bool:
           return self.value() > limit.value()
   ```

### ✅ Good Uses of Primitives

1. **JSON Specification** (core/json.spl)
   ```simple
   pub enum JsonValue:
       bool(bool)        # JSON spec requires primitive bool
       Number(f64)       # JSON spec requires f64
   ```

2. **Mathematical Functions** (core/math.spl)
   ```simple
   pub fn lerp(a: f32, b: f32, t: f32) -> f32  # Generic interpolation
   pub fn sin(x: f32) -> f32                   # Trigonometric function
   ```

3. **Predicates** (everywhere)
   ```simple
   pub fn is_empty() -> bool       # Universal pattern
   pub fn has_field(name: text) -> bool
   ```

---

## Related Documents

- [Primitive API Migration Report](../report/primitive_api_migration_complete_2026-01-20.md) - Implementation details
- [Type System Features](../design/type_system_features.md) - Simple's type system
- [Question Mark Design Decision](../design/question_mark_design_decision.md) - Related syntax decisions

---

**Document Version**: 1.0
**Last Updated**: 2026-01-20
**Status**: Complete - Production Guidance
