# Migration Verification Checklist

**Purpose:** Ensure Simple migrations preserve all performance, robustness, features, and logic from Rust originals.

## Pre-Migration Analysis

### 1. Code Structure Inventory
- [ ] Count all structs/enums/types
- [ ] Count all functions/methods
- [ ] List all public APIs
- [ ] Identify all dependencies
- [ ] Note all constants and statics

### 2. Logic Complexity Assessment
- [ ] Identify critical paths (performance-sensitive)
- [ ] Map all error handling branches
- [ ] Note all edge cases
- [ ] List all optimizations
- [ ] Document algorithmic complexity (O(n), O(log n), etc.)

### 3. Feature Completeness
- [ ] List all language features used (generics, traits, lifetimes, etc.)
- [ ] Identify special Rust patterns (Option, Result, Iterator, etc.)
- [ ] Note all unsafe blocks (need special handling)
- [ ] Check for platform-specific code

## During Migration

### 4. Type System Preservation
- [ ] All structs have same fields with correct types
- [ ] All enums have same variants with same data
- [ ] Generic parameters preserved (T, U, etc.)
- [ ] Type constraints preserved (bounds, traits)

### 5. Logic Equivalence
- [ ] All match branches handled identically
- [ ] All if/else conditions preserved
- [ ] Loop logic identical (for, while, iterator chains)
- [ ] Early returns preserved
- [ ] All side effects maintained

### 6. Error Handling Robustness
- [ ] All Result types preserved
- [ ] All Option handling preserved
- [ ] All panic/error messages preserved
- [ ] All error recovery paths identical

### 7. Performance Characteristics
- [ ] Algorithm complexity unchanged (O(n) → O(n))
- [ ] No accidental copies where moves existed
- [ ] Iterator chains not materialized unnecessarily
- [ ] No redundant allocations introduced
- [ ] Short-circuit evaluation preserved

### 8. API Compatibility
- [ ] All public functions have identical signatures
- [ ] All method receivers correct (self, &self, &mut self → fn, me)
- [ ] Return types match exactly
- [ ] Parameter order preserved

## Post-Migration Verification

### 9. Line-by-Line Comparison
- [ ] Read Rust version fully
- [ ] Read Simple version fully
- [ ] Compare side-by-side for each function
- [ ] Verify each branch, each expression

### 10. Test Coverage
- [ ] All unit tests ported (if any)
- [ ] All doc tests ported (if any)
- [ ] All integration tests still pass
- [ ] Edge cases explicitly tested

### 11. Build Verification
- [ ] Simple version compiles without errors
- [ ] No warnings introduced
- [ ] Module exports correct
- [ ] Dependencies resolve

### 12. Documentation Preservation
- [ ] All doc comments preserved
- [ ] All examples preserved
- [ ] All design notes preserved
- [ ] Port header preserved

## Critical Checks for Semantics

### Performance-Critical Patterns
```rust
// Rust: Short-circuit evaluation
if expensive_check() && another_check() { }

// Simple: MUST preserve short-circuit
if expensive_check() and another_check():
```

### Robustness Patterns
```rust
// Rust: Explicit bounds checking
if value >= min && value <= max { }

// Simple: MUST preserve both bounds
if value >= min and value <= max:
```

### Feature Preservation
```rust
// Rust: Generic Result<T, E>
pub fn coerce<T>(...) -> Result<T, String>

// Simple: MUST preserve generics
fn coerce<T>(...) -> Result<T, text>
```

### Logic Preservation
```rust
// Rust: All match arms
match value {
    Variant1(x) => handle1(x),
    Variant2(y) => handle2(y),
    Variant3 => default(),
}

// Simple: MUST have all arms
match value:
    case Variant1(x): handle1(x)
    case Variant2(y): handle2(y)
    case Variant3: default()
```

## Red Flags (Stop and Review)

⛔ **Performance Degradation:**
- Accidentally converting O(1) to O(n)
- Materializing iterators unnecessarily
- Adding extra allocations

⛔ **Logic Errors:**
- Missing match branch
- Inverted condition
- Wrong operator precedence

⛔ **Robustness Issues:**
- Missing error handling
- Removed bounds check
- Lost overflow check

⛔ **Feature Loss:**
- Generic parameter removed
- Type safety weakened
- API changed

## Migration Report Template

```markdown
# Migration Report: [Module Name]

## Verification Checklist
- [x] All types preserved (N structs, M enums)
- [x] All functions preserved (K functions)
- [x] All logic branches preserved
- [x] All error handling preserved
- [x] Performance characteristics preserved
- [x] API compatibility maintained

## Comparison
| Aspect | Rust | Simple | Status |
|--------|------|--------|--------|
| Structs | N | N | ✅ |
| Enums | M | M | ✅ |
| Functions | K | K | ✅ |
| Lines | L | L' | ✅ (X% reduction) |

## Critical Paths Verified
- [x] Function A: Logic identical
- [x] Function B: Error handling preserved
- [x] Function C: Performance preserved

## Testing
- [x] Unit tests ported: X tests
- [x] All tests pass
- [x] Edge cases verified

## Sign-off
✅ All performance, robustness, features, and logic preserved.
```

## Usage

For each migration:
1. Read this checklist
2. Go through Pre-Migration Analysis
3. Perform migration with During Migration checks
4. Execute Post-Migration Verification
5. Create Migration Report
6. Only commit if all checks pass
