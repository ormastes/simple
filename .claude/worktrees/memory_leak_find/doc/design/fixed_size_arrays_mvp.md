# Fixed-Size Arrays - MVP Implementation Plan

**Feature**: `[T; N]` syntax with compile-time size checking
**Estimated Effort**: 18-26 hours (full implementation)
**MVP Effort**: 6-8 hours (runtime checking only)

---

## Requirements from Tests

### Core Features
1. ✅ Syntax: `val vec3: [f64; 3] = [1.0, 2.0, 3.0]`
2. ✅ Size validation: Reject wrong-sized arrays
3. ✅ Mutation rejection: No push/pop/insert/remove/clear
4. ✅ Read operations: len, get, indexing, map, filter work
5. ✅ Nested arrays: `[[f64; 3]; 3]`

---

## Implementation Approaches

### Option A: Full Type System Integration (18-26 hours)
**Changes**:
1. Parser: Support `[T; N]` syntax in types
2. Type system: Track array size in type
3. Type checker: Validate sizes at compile time
4. Codegen: Specialized fixed-size array ops

**Pros**:
- Compile-time errors
- Best performance
- Clean type system

**Cons**:
- Long implementation time
- Touches many subsystems

### Option B: Runtime Validation (6-8 hours) ⭐ **RECOMMENDED MVP**
**Changes**:
1. Value enum: Add FixedSizeArray variant
2. Type annotation: Parse `[T; N]` as string, extract size
3. Let binding: Check size at runtime, wrap in FixedSizeArray
4. Method dispatch: Reject mutations on FixedSizeArray

**Pros**:
- Faster implementation
- Works for most use cases
- Can upgrade to Option A later

**Cons**:
- Runtime errors instead of compile errors
- Slight performance overhead

### Option C: Hybrid (10-14 hours)
**Changes**:
- Parser support for `[T; N]`
- Runtime size checking
- Deferred compile-time checking

---

## MVP Implementation (Option B)

### Step 1: Add FixedSizeArray Variant (30 min)
```rust
// rust/compiler/src/value.rs
pub enum Value {
    // ... existing variants ...
    Array(Vec<Value>),
    FrozenArray(Arc<Vec<Value>>),

    /// Fixed-size array with compile-time/runtime size checking
    /// size: expected size, data: actual values
    FixedSizeArray { size: usize, data: Vec<Value> },

    // ...
}
```

### Step 2: Parse `[T; N]` Type Annotations (1-2 hours)
Extract size from type annotation:
```rust
// In node_exec.rs, when handling Let binding:
if let Some(Type::Array(inner_ty)) = &type_annotation {
    // Check if it's [T; N] format by parsing the type string
    // Extract N from annotation
    if let Some(size) = extract_fixed_size(inner_ty) {
        // Validate array size matches
        if let Value::Array(vec) = &value {
            if vec.len() != size {
                return Err(...); // Size mismatch error
            }
            // Wrap in FixedSizeArray
            value = Value::FixedSizeArray {
                size,
                data: vec.clone(),
            };
        }
    }
}
```

### Step 3: Method Dispatch for FixedSizeArray (2-3 hours)
```rust
// In interpreter_method/mod.rs
Value::FixedSizeArray { size, data } => {
    // Delegate read-only ops to array handler
    if let Some(result) = collections::handle_fixed_size_array_methods(
        size,
        data,
        method,
        args,
        ...
    )? {
        return Ok(result);
    }
}

// In collections.rs
pub fn handle_fixed_size_array_methods(...) {
    match method {
        // Reject mutations
        "push" | "pop" | "insert" | "remove" | "clear" => {
            Err(CompileError::semantic(
                "Cannot call {}() on fixed-size array", method
            ))
        }
        // Allow all read operations
        _ => handle_array_methods(data, method, args, ...)
    }
}
```

### Step 4: Helper Functions (1-2 hours)
```rust
/// Extract size from [T; N] type annotation
fn extract_fixed_size(ty: &Type) -> Option<usize> {
    // Parse type string to find "; N]" pattern
    // Return Some(N) if found, None otherwise
}

/// Create fixed-size array value
impl Value {
    pub fn fixed_size_array(size: usize, data: Vec<Value>) -> Result<Self, String> {
        if data.len() != size {
            return Err(format!("Size mismatch: expected {}, got {}", size, data.len()));
        }
        Ok(Value::FixedSizeArray { size, data })
    }
}
```

### Step 5: Update Display/Debug (30 min)
Handle FixedSizeArray in:
- Display implementation
- Debug implementation
- Equality checks
- Clone implementation

---

## Testing Strategy

### Unit Tests
```rust
#[test]
fn test_fixed_size_array_creation() {
    let arr = Value::fixed_size_array(3, vec![
        Value::Int(1),
        Value::Int(2),
        Value::Int(3),
    ]).unwrap();
    // Assert it's FixedSizeArray
}

#[test]
fn test_fixed_size_rejects_mutations() {
    // Try push/pop on FixedSizeArray
    // Assert error
}
```

### Integration Tests
Run the SSpec tests:
- `fixed_size_arrays_spec.spl` (28 tests)
- `fixed_size_edge_cases_spec.spl` (15 tests)

Expected pass rate: 60-70% (runtime checks work, compile-time checks deferred)

---

## Limitations of MVP

### What Works ✅
- Runtime size validation
- Mutation rejection
- Read operations (len, get, etc.)
- Nested arrays
- Clear error messages

### What Doesn't Work ❌
- Compile-time size checking (errors at runtime)
- Type inference for size
- Size-based overloading
- Zero-cost abstraction

### Upgrade Path
Later can add:
1. Parser support for `[T; N]`
2. Type system size tracking
3. Compile-time validation
4. Optimized codegen

---

## Implementation Order

1. ✅ Add FixedSizeArray variant (30 min)
2. ✅ Add helper constructor (30 min)
3. ✅ Extract size from type annotation (1-2 hours)
4. ✅ Update Let binding handler (1 hour)
5. ✅ Add method dispatch (2-3 hours)
6. ✅ Update display/debug (30 min)
7. ✅ Write unit tests (1 hour)
8. ✅ Test with SSpec (1 hour)

**Total**: 6-8 hours for MVP

---

## Decision

**Recommend**: Implement MVP (Option B) now
- Gets core functionality working quickly
- Can upgrade to full type system later
- Unblocks users who need fixed-size arrays

**Defer**: Full type system integration (Option A)
- Complex, touches many systems
- Can be added incrementally
- Not critical for initial use

---

## Files to Modify

1. `rust/compiler/src/value.rs` - Add FixedSizeArray variant
2. `rust/compiler/src/interpreter/node_exec.rs` - Let binding validation
3. `rust/compiler/src/interpreter_method/mod.rs` - Dispatch
4. `rust/compiler/src/interpreter_method/collections.rs` - Handler
5. `rust/compiler/src/value_impl.rs` - Display/Debug (if exists)

**Estimated**: 5 files, ~200-300 lines of code
