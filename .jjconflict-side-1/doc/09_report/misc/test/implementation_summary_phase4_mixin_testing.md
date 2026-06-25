# Mixin Implementation - Phase 4: Testing and Integration

**Date:** 2026-01-08  
**Phase:** 4 of 5  
**Status:** 🚧 Documented (Implementation Pending)

## Overview

Phase 4 focuses on comprehensive testing of mixin functionality and ensuring the implementation works correctly across the full compiler pipeline (AST → HIR → MIR → Codegen).

## Prerequisites

**Phase 3 Complete:**
- ✅ HIR type system supports `HirType::Mixin`
- ✅ `register_mixin()` lowers AST mixins to HIR
- ✅ `register_class()` expands mixin fields into classes
- ✅ Mixin methods are lowered in second pass
- ✅ Lean verification code generation updated

**Key Insight:**
MIR (Mid-level IR) does NOT need special mixin handling because:
- HIR already flattens mixins into their application targets
- By the time code reaches MIR, mixin fields are regular class fields
- Mixin methods are regular functions with the class as `self` context
- This design choice simplifies the compiler pipeline

## Test Strategy

### 1. Parser Tests (Unit Level)

**Location:** `src/parser/src/tests/`

Test mixin syntax parsing:

```rust
#[test]
fn test_parse_basic_mixin() {
    let source = r#"
        mixin Timestamped {
            field created_at: i64
            field updated_at: i64
            
            fn get_age() -> i64 {
                self.updated_at - self.created_at
            }
        }
    "#;
    
    let module = parse_source(source).unwrap();
    // Assert mixin parsed correctly
}

#[test]
fn test_parse_generic_mixin() {
    let source = r#"
        mixin Comparable<T> where T: Ord {
            fn compare(other: T) -> i32
        }
    "#;
    // Test generic params and trait bounds
}

#[test]
fn test_parse_mixin_application() {
    let source = r#"
        class Document {
            use Timestamped
            field title: str
        }
    "#;
    // Test 'use MixinName' in class body
}
```

### 2. Type System Tests (Integration Level)

**Location:** `src/type/tests/`

Test type checking with mixins:

```rust
#[test]
fn test_mixin_field_access() {
    // Verify accessing mixin fields works
}

#[test]
fn test_mixin_method_call() {
    // Verify calling mixin methods works
}

#[test]
fn test_mixin_type_parameter_substitution() {
    // Test generic mixin type parameter resolution
}

#[test]
fn test_mixin_trait_bound_checking() {
    // Verify trait bounds are enforced
}
```

### 3. HIR Lowering Tests

**Location:** `src/compiler/src/hir/lower/tests/`

Test AST → HIR lowering:

```rust
#[test]
fn test_lower_mixin_to_hir() {
    // Verify MixinDef → HirType::Mixin
}

#[test]
fn test_mixin_field_expansion() {
    // Verify mixin fields added to class
}

#[test]
fn test_mixin_method_lowering() {
    // Verify mixin methods become HirFunctions
}
```

### 4. End-to-End Tests

**Location:** `tests/*.simple`

Real Simple source files testing complete pipeline:

**4.1 Basic Mixin (`tests/mixin_basic.simple`)**
```simple
mixin Timestamped {
    field created_at: i64
    field updated_at: i64
    
    fn get_age() -> i64 {
        self.updated_at - self.created_at
    }
}

class Document {
    field title: str
    use Timestamped
}

fn main() -> i32 {
    let doc = Document { title: "Test", created_at: 0, updated_at: 100 }
    doc.get_age()  # Should return 100
}
```

**4.2 Generic Mixin (`tests/mixin_generic.simple`)**
```simple
mixin Container<T> {
    field items: [T]
    
    fn size() -> i32 {
        self.items.len()
    }
}

class StringList {
    use Container<str>
}

fn main() -> i32 {
    let list = StringList { items: ["a", "b", "c"] }
    list.size()  # Should return 3
}
```

**4.3 Multiple Mixins (`tests/mixin_multiple.simple`)**
```simple
mixin Identifiable {
    field id: i64
}

mixin Timestamped {
    field created_at: i64
}

class User {
    field name: str
    use Identifiable
    use Timestamped
}

fn main() -> i32 {
    let u = User { name: "Alice", id: 1, created_at: 0 }
    u.id as i32
}
```

**4.4 Mixin with Trait Bounds (`tests/mixin_traits.simple`)**
```simple
mixin Comparable<T> where T: Ord {
    fn is_greater(other: T) -> bool {
        self > other
    }
}

class Counter {
    field value: i32
    use Comparable<i32>
}
```

**4.5 Mixin with Required Methods (`tests/mixin_required.simple`)**
```simple
mixin Serializable {
    fn to_json() -> str
    
    fn serialize() -> str {
        "{ data: " + self.to_json() + " }"
    }
}

class Document {
    field title: str
    use Serializable
    
    # Must implement to_json()
    fn to_json() -> str {
        "\"" + self.title + "\""
    }
}
```

### 5. BDD/Gherkin Tests

**Location:** `specs/features/mixins.feature`

```gherkin
Feature: Mixin Composition
  As a Simple programmer
  I want to compose behavior using mixins
  So that I can reuse code without inheritance

  Scenario: Define and use a basic mixin
    Given a mixin definition "Timestamped"
    And a class "Document" using "Timestamped"
    When I create a Document instance
    Then the instance should have mixin fields
    And the instance should support mixin methods

  Scenario: Use generic mixin
    Given a generic mixin "Container<T>"
    And a class "StringList" using "Container<str>"
    When I instantiate StringList
    Then type parameter T should be resolved to str

  Scenario: Multiple mixin composition
    Given mixins "Identifiable" and "Timestamped"
    And a class using both mixins
    Then all mixin fields should be available
    And no field name conflicts should occur
```

## Expected Behavior

### Field Resolution
- Mixin fields appear as regular fields in the class
- Field access syntax: `object.mixin_field`
- Field initialization required in constructor

### Method Resolution
- Mixin methods callable on class instances
- `self` in mixin methods refers to the class instance
- Method dispatch is static (resolved at compile time)

### Type Parameter Substitution
- Generic mixin `Container<T>` applied as `use Container<str>`
- Type parameter `T` replaced with `str` throughout mixin body
- Type checking enforces correct substitution

### Trait Bounds
- Mixin can require traits: `where T: Ord`
- Compiler verifies type arguments satisfy bounds
- Error if bound not satisfied

### Required Methods
- Mixin can declare required methods
- Class must implement required methods
- Compiler error if not implemented

## Error Cases to Test

```simple
# Error: Missing required method
mixin Serializable {
    fn to_json() -> str
}

class Document {
    use Serializable
    # ERROR: must implement to_json()
}

# Error: Field name conflict
mixin A { field x: i32 }
mixin B { field x: i64 }

class C {
    use A
    use B  # ERROR: field 'x' conflicts
}

# Error: Type parameter mismatch
mixin Container<T> {
    field items: [T]
}

class StringList {
    use Container<i32>  # Applied with i32
    field items: [str]  # ERROR: type mismatch
}

# Error: Trait bound not satisfied
mixin Comparable<T> where T: Ord {
    fn compare(other: T) -> i32
}

class MyClass {
    use Comparable<SomeNonOrdType>  # ERROR: SomeNonOrdType doesn't impl Ord
}
```

## Implementation Tasks

### Phase 4 Checklist

- [ ] **Parser Tests**
  - [ ] Basic mixin definition parsing
  - [ ] Generic mixin parsing
  - [ ] Mixin application (`use MixinName`) parsing
  - [ ] Required methods parsing
  - [ ] Trait bounds parsing

- [ ] **Type System Tests**
  - [ ] Field access type checking
  - [ ] Method call type checking
  - [ ] Generic type parameter resolution
  - [ ] Trait bound verification
  - [ ] Required method verification

- [ ] **HIR Tests**
  - [ ] Mixin registration
  - [ ] Field expansion into classes
  - [ ] Method lowering
  - [ ] Type parameter substitution

- [ ] **Integration Tests**
  - [ ] Basic mixin end-to-end
  - [ ] Generic mixin end-to-end
  - [ ] Multiple mixins composition
  - [ ] Trait bounds enforcement
  - [ ] Required methods checking

- [ ] **BDD Tests**
  - [ ] Write `.feature` files
  - [ ] Implement step definitions
  - [ ] Run cucumber tests

- [ ] **Error Handling**
  - [ ] Missing required methods error
  - [ ] Field name conflicts error
  - [ ] Type mismatch errors
  - [ ] Trait bound violations error

- [ ] **Documentation**
  - [ ] Update language reference
  - [ ] Add mixin usage examples
  - [ ] Document best practices
  - [ ] Update error message guide

## Next Phase

**Phase 5: Optimization and Refinement**
- Performance optimization
- Memory layout optimization
- Better error messages
- IDE integration (syntax highlighting, autocomplete)
- Lean formal verification theorems

## References

- Phase 1: Grammar and Parser (Complete)
- Phase 2: Type System (Complete)
- Phase 3: HIR Lowering (Complete)
- Related: Type inference, Trait system, Generic types
