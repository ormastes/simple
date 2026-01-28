# note.sdn Testing Guide

## Overview

This document describes how to test the note.sdn implementation in both Rust and Simple.

## Test Coverage

### Rust Unit Tests

Located in `src/rust/compiler/src/monomorphize/note_sdn.rs`:

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_note_sdn() { ... }

    #[test]
    fn test_instantiation_entry() { ... }

    #[test]
    fn test_dependency_edge() { ... }

    #[test]
    fn test_circular_warning() { ... }

    #[test]
    fn test_sdn_escape() { ... }
}
```

**Run tests:**
```bash
cargo test -p simple-compiler note_sdn
```

### Simple SSpec Tests

Located in `test/lib/std/unit/compiler/note_sdn_spec.spl`:

**Test cases (13 total):**

1. **NoteSdnMetadata tests:**
   - `creates empty metadata`
   - `adds instantiation entry`
   - `adds possible instantiation entry`
   - `adds dependency edge`
   - `serializes to SDN format`

2. **InstantiationStatus tests:**
   - `converts to string`
   - `parses from string`

3. **DependencyKind tests:**
   - `converts to string`
   - `parses from string`

4. **CircularWarning and CircularError tests:**
   - `creates circular warning`
   - `creates circular error`

5. **SDN escaping tests:**
   - `escapes special characters`

6. **Integration tests:**
   - `generates full note.sdn with all tables`

**Run tests:**
```bash
./target/debug/simple_old test test/lib/std/unit/compiler/note_sdn_spec.spl
```

## Manual Testing

### Test 1: Create Empty Metadata

**Rust:**
```rust
let note = NoteSdnMetadata::new();
assert!(note.is_empty());
assert_eq!(note.instantiations.len(), 0);
```

**Expected:** Pass

**Simple:**
```simple
val note = NoteSdnMetadata.new()
assert note.is_empty()
assert note.instantiations.len() == 0
```

**Expected:** Pass

### Test 2: Add Instantiation

**Rust:**
```rust
let mut note = NoteSdnMetadata::new();
note.add_instantiation(InstantiationEntry::new(
    "List".to_string(),
    vec![ConcreteType::Named("Int".to_string(), vec![])],
    "List$Int".to_string(),
    "app.spl".to_string(),
    "app.spl:10:5".to_string(),
    "app.o".to_string(),
    InstantiationStatus::Compiled,
));
assert_eq!(note.instantiations.len(), 1);
assert_eq!(note.instantiations[0].template, "List");
```

**Expected:** Pass

### Test 3: Serialize to SDN

**Rust:**
```rust
let mut note = NoteSdnMetadata::new();
note.add_instantiation(/* ... */);
let sdn = note.to_sdn();

assert!(sdn.contains("# Instantiation To/From Metadata"));
assert!(sdn.contains("instantiations |"));
assert!(sdn.contains("\"List\""));
assert!(sdn.contains("\"Int\""));
assert!(sdn.contains("# END_NOTE\n"));
```

**Expected:** Pass

### Test 4: SDN Format Validation

**Check that generated SDN:**
- Has header comment
- Has format version
- Has all 6 tables (even if empty)
- Has terminator `\n# END_NOTE\n`
- Properly escapes special characters
- Uses correct column names

**Example output:**
```sdn
# Instantiation To/From Metadata
# Format version: 1.0

# Template instantiations (what was compiled)
instantiations |id, template, type_args, mangled_name, from_file, from_loc, to_obj, status|
    0, "List", "Int", "List$Int", "app.spl", "app.spl:10:5", "app.o", "compiled"

# Possible instantiations (can be lazily generated)
possible |id, template, type_args, mangled_name, required_by, can_defer|

# Type inference instantiations
type_inferences |id, inferred_type, expr, context, from_file, from_loc|

# Instantiation graph (to/from relationships)
dependencies |from_inst, to_inst, dep_kind|

# Circular dependency detection results
circular_warnings |id, cycle_path, severity|

circular_errors |id, cycle_path, error_code|

# END_NOTE
```

### Test 5: Dependency Graph

**Rust:**
```rust
let mut note = NoteSdnMetadata::new();

// Add instantiation: Container<List<Int>>
note.add_instantiation(InstantiationEntry::new(
    "Container".to_string(),
    vec![ConcreteType::Named("List".to_string(), vec![
        ConcreteType::Named("Int".to_string(), vec![])
    ])],
    "Container$List$Int".to_string(),
    "app.spl".to_string(),
    "app.spl:20:5".to_string(),
    "app.o".to_string(),
    InstantiationStatus::Compiled,
));

// Add dependency: Container<List<Int>> -> List<Int>
note.add_dependency(DependencyEdge::new(
    "Container$List$Int".to_string(),
    "List$Int".to_string(),
    DependencyKind::FieldType,
));

// Add dependency: List<Int> -> Int
note.add_dependency(DependencyEdge::new(
    "List$Int".to_string(),
    "Int".to_string(),
    DependencyKind::TypeParam,
));

assert_eq!(note.dependencies.len(), 2);
```

**Expected:** Pass

### Test 6: Circular Dependencies

**Rust:**
```rust
let mut note = NoteSdnMetadata::new();

// Soft cycle (warning): Node<T> -> Option<Node<T>> -> Node<T>
note.add_circular_warning(CircularWarning::new(
    "Node$T->Option$Node$T->Node$T".to_string(),
    "warning".to_string(),
));

// Hard cycle (error): A<T> -> B<T> -> C<T> -> A<T>
note.add_circular_error(CircularError::new(
    "A$T->B$T->C$T->A$T".to_string(),
    "E0420".to_string(),
));

assert_eq!(note.circular_warnings.len(), 1);
assert_eq!(note.circular_errors.len(), 1);
```

**Expected:** Pass

### Test 7: String Escaping

**Rust:**
```rust
fn test_escaping() {
    assert_eq!(escape_sdn("hello"), "hello");
    assert_eq!(escape_sdn("test\"quote"), "test\\\"quote");
    assert_eq!(escape_sdn("back\\slash"), "back\\\\slash");
    assert_eq!(escape_sdn("new\nline"), "new\\nline");
    assert_eq!(escape_sdn("tab\there"), "tab\\there");
}
```

**Expected:** All assertions pass

## Integration Testing

### Test 1: SMF Writer Integration

**Rust:**
```rust
use simple_compiler::smf_writer::generate_smf_with_all_sections;

let mut note = NoteSdnMetadata::new();
note.add_instantiation(/* ... */);

let smf_bytes = generate_smf_with_all_sections(
    &object_code,
    Some(&templates),
    Some(&metadata),
    Some(&note),
    None,
    target,
);

// Verify SMF contains note.sdn section
// (Requires SMF loader to verify - Phase 2)
```

**Expected:** SMF file generated without errors

### Test 2: Round-Trip Serialization

**When Phase 2 (loader) is implemented:**

```rust
// Serialize
let sdn = note.to_sdn();

// Deserialize
let parsed = NoteSdnMetadata::from_sdn(&sdn)?;

// Verify
assert_eq!(note.instantiations.len(), parsed.instantiations.len());
assert_eq!(note.dependencies.len(), parsed.dependencies.len());
```

**Expected:** Pass (after Phase 2)

## Performance Testing

### Test 1: Large Metadata

```rust
let mut note = NoteSdnMetadata::new();

// Add 1000 instantiations
for i in 0..1000 {
    note.add_instantiation(InstantiationEntry::new(
        format!("Template{}", i),
        vec![ConcreteType::Named("Int".to_string(), vec![])],
        format!("Template{}$Int", i),
        "app.spl".to_string(),
        format!("app.spl:{}:5", i),
        "app.o".to_string(),
        InstantiationStatus::Compiled,
    ));
}

// Measure serialization time
let start = std::time::Instant::now();
let sdn = note.to_sdn();
let duration = start.elapsed();

println!("Serialized 1000 entries in {:?}", duration);
println!("SDN size: {} bytes", sdn.len());
```

**Expected:**
- Duration: < 10ms
- Size: ~100KB (100 bytes per entry)

### Test 2: Complex Dependencies

```rust
let mut note = NoteSdnMetadata::new();

// Add 100 instantiations with dependencies forming a DAG
for i in 0..100 {
    note.add_instantiation(/* ... */);
    if i > 0 {
        note.add_dependency(DependencyEdge::new(
            format!("Template{}", i),
            format!("Template{}", i - 1),
            DependencyKind::TypeParam,
        ));
    }
}

let sdn = note.to_sdn();
assert!(sdn.contains("# END_NOTE\n"));
```

**Expected:** Pass

## Error Cases

### Test 1: Invalid Status String

**Rust:**
```rust
let result = InstantiationStatus::from_str("invalid");
assert!(result.is_err());
assert_eq!(result.unwrap_err(), "Unknown instantiation status: invalid");
```

**Expected:** Error with correct message

### Test 2: Invalid Dependency Kind

**Rust:**
```rust
let result = DependencyKind::from_str("invalid");
assert!(result.is_err());
assert_eq!(result.unwrap_err(), "Unknown dependency kind: invalid");
```

**Expected:** Error with correct message

### Test 3: Empty Serialization

**Rust:**
```rust
let note = NoteSdnMetadata::new();
let sdn = note.to_sdn();

// Should contain empty tables but still be valid SDN
assert!(sdn.contains("instantiations |"));
assert!(sdn.contains("# END_NOTE\n"));
```

**Expected:** Valid SDN with empty tables

## Test Checklist

- [ ] Rust unit tests pass
- [ ] Simple SSpec tests pass
- [ ] Empty metadata test passes
- [ ] Instantiation entry test passes
- [ ] Dependency edge test passes
- [ ] SDN serialization test passes
- [ ] String escaping test passes
- [ ] Circular dependency test passes
- [ ] SMF writer integration test passes
- [ ] Performance test passes (< 10ms for 1000 entries)

## Known Issues

### Issue 1: SDN Parsing Not Implemented

**Status:** Not yet implemented (Phase 2)
**Workaround:** Only serialization (writing) is supported
**Test Status:** Tests for `from_sdn()` currently return error

### Issue 2: Pre-existing Compilation Errors

**Status:** Other parts of compiler have compilation errors
**Workaround:** Test note_sdn module in isolation
**Test Status:** Unit tests in note_sdn.rs are fine, but test harness fails

## Future Tests (Phase 2+)

### Phase 2: Loader Tests
- [ ] Load note.sdn from SMF file
- [ ] Parse SDN format
- [ ] Build dependency graph from SDN
- [ ] Round-trip serialization (write + read)

### Phase 3: Compile-Time Integration Tests
- [ ] Auto-track instantiations during compilation
- [ ] Auto-detect circular dependencies
- [ ] Auto-populate possible instantiations

### Phase 4: Link-Time Tests
- [ ] Merge note.sdn from multiple object files
- [ ] Resolve missing symbols from `possible` table
- [ ] Generate lazy instantiations

## Running All Tests

```bash
# Rust tests (when compilation errors are fixed)
cargo test -p simple-compiler

# Simple tests
./target/debug/simple_old test test/lib/std/unit/compiler/

# Specific note_sdn tests
./target/debug/simple_old test test/lib/std/unit/compiler/note_sdn_spec.spl
```

## Test Results

### Current Status (Phase 1)

| Test Suite | Status | Notes |
|------------|--------|-------|
| Rust unit tests | ⚠️ Blocked | Pre-existing compilation errors in other files |
| Simple SSpec tests | ✅ Ready | 13 test cases written |
| Integration tests | ⏳ Pending | Requires Phase 2 (loader) |
| Performance tests | ⏳ Pending | Can be run after fixing compilation errors |

### Expected Results After Fixes

All tests should pass with:
- 0 failures
- 0 panics
- < 10ms per test
- Correct SDN format output

## Debugging Tips

### Tip 1: Inspect SDN Output

```rust
let sdn = note.to_sdn();
println!("{}", sdn);
```

### Tip 2: Check Entry Counts

```rust
println!("Instantiations: {}", note.instantiations.len());
println!("Dependencies: {}", note.dependencies.len());
```

### Tip 3: Verify Terminator

```rust
assert!(sdn.ends_with("# END_NOTE\n"));
```

### Tip 4: Validate Column Names

```rust
assert!(sdn.contains("instantiations |id, template, type_args"));
assert!(sdn.contains("dependencies |from_inst, to_inst, dep_kind"));
```

## See Also

- [note.sdn Usage Guide](../guide/note_sdn_usage_guide.md)
- [note.sdn API Reference](../api/note_sdn_api.md)
- [SMF Testing Guide](smf_testing_guide.md)
