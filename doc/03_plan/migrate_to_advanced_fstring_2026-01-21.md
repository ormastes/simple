# Plan: Migrate Current Code to Advanced FString Instantiation

**Date:** 2026-01-21
**Status:** Phase 2 Complete
**Depends On:** `advanced_fstring_instantiation_2026-01-21.md`

## Overview

Migrate the current explicit type annotation approach to the ergonomic `.with` syntax.

### Current (Verbose)
```simple
val template = "Welcome {user} to {city}"
val data: Dict<template.keys, String> = {"user": name, "city": loc}
val result = template.format(data)
```

### Target (Ergonomic)
```simple
val template = "Welcome {user} to {city}"
val result = template.with {"user": name, "city": loc}
```

> **Note:** The preferred syntax is `.with {...}` without parentheses.
> The parser has been updated to support this ergonomic syntax.

---

## Two-Phase Migration Strategy

### Phase 1: Quick Win (No Type System Changes)
- Implement `.with` for FString **literals** and **local variables**
- Use existing `fstring_const_keys` tracking infrastructure
- No `Type::FString` variant needed

**Scope:**
| Case | Supported |
|------|-----------|
| `"Hello {x}".with {...}` | Yes (literal) |
| `val t = "..."; t.with {...}` | Yes (local var lookup) |
| `fn format(t): t.with {...}` | No (Phase 2) |
| `get_template().with {...}` | No (Phase 2) |

### Phase 2: Full Generality (Type System Enhancement)
- Add `Type::FString { const_keys }` variant
- FString inference returns `FString` type (not `Str`)
- Full support for passing FStrings through functions

---

## Phase 1 Implementation

### Step 1.1: Keep Current Infrastructure

The current implementation provides foundation:
- `Type::ConstKeySet` - compile-time key sets
- `Type::DependentKeys` - reference to FString keys
- `fstring_const_keys` tracking in TypeChecker
- `resolve_dependent_keys()` resolution
- `validate_dict_const_keys()` validation

**Action:** No changes - keep as internal infrastructure

### Step 1.2: Implement `.with` Method Resolution (No Type Changes)

When type checker sees `expr.with dict_expr`:
1. Check if receiver is FString literal → extract keys from AST
2. Check if receiver is identifier → lookup in `fstring_const_keys`
3. Validate dict_expr keys against extracted keys
4. Return `Type::Str`

```rust
// In checker_infer.rs, handle MethodCall
Expr::MethodCall { receiver, method, args, .. } => {
    let recv_ty = self.infer_expr(receiver)?;

    // Phase 1: Handle .with for FString literals and tracked variables
    if method == "with" {
        if let Some(const_keys) = self.get_fstring_keys_from_expr(receiver) {
            // Validate dict argument
            if let Some(arg) = args.first() {
                let expected_ty = Type::Dict {
                    key: Box::new(Type::ConstKeySet { keys: const_keys }),
                    value: Box::new(Type::Str),
                };
                self.validate_dict_const_keys(&arg.value, &expected_ty)?;
            }
            return Ok(Type::Str);
        }
    }
    // ... rest of method call handling
}

/// Extract const_keys from FString expression (Phase 1 approach)
fn get_fstring_keys_from_expr(&self, expr: &Expr) -> Option<Vec<String>> {
    match expr {
        // Case 1: Direct FString literal
        Expr::FString { type_meta, .. } => type_meta.const_keys().cloned(),
        // Case 2: Variable referencing FString
        Expr::Identifier(name) => self.fstring_const_keys.get(name).cloned(),
        _ => None,
    }
}
```

**Files to modify:**
- `src/rust/type/src/checker_infer.rs` - Add `.with` handling and helper method

### Step 1.3: Add Unit Tests for Phase 1

```rust
#[test]
fn test_fstring_with_literal_valid_keys() {
    let code = r#"
        val r = "Hello {name}".with {"name": "Alice"}
    "#;
    assert!(type_check(code).is_ok());
}

#[test]
fn test_fstring_with_variable_valid_keys() {
    let code = r#"
        val t = "Hello {name}"
        val r = t.with {"name": "Alice"}
    "#;
    assert!(type_check(code).is_ok());
}

#[test]
fn test_fstring_with_invalid_key() {
    let code = r#"
        val t = "Hello {name}"
        val r = t.with {"nam": "Alice"}
    "#;
    assert!(type_check(code).is_err());
}
```

### Phase 1 File Summary

| File | Changes |
|------|---------|
| `src/rust/type/src/checker_infer.rs` | `.with` handling, `get_fstring_keys_from_expr()` |
| `src/rust/type/tests/const_keys_spec.rs` | Unit tests |

---

## Phase 2 Implementation

### Step 2.1: Add FString Type Variant

Current: FString infers to `Type::Str`
Target: FString infers to `Type::FString { const_keys }`

```rust
// In src/rust/type/src/lib.rs
pub enum Type {
    // ... existing variants ...

    /// Format string with compile-time known placeholders
    FString {
        const_keys: Vec<String>,
    },
}
```

**Files to modify:**
- `src/rust/type/src/lib.rs` - Add Type::FString variant
- `src/rust/type/src/checker_infer.rs` - Return FString type
- `src/rust/type/src/checker_unify.rs` - Handle FString unification

### Step 2.2: Update `.with` to Use Type System

```rust
// In checker_infer.rs, updated MethodCall handling
Expr::MethodCall { receiver, method, args, .. } => {
    let recv_ty = self.infer_expr(receiver)?;

    if method == "with" {
        // Phase 2: Use type system
        if let Type::FString { const_keys } = &recv_ty {
            if let Some(arg) = args.first() {
                let expected_ty = Type::Dict {
                    key: Box::new(Type::ConstKeySet { keys: const_keys.clone() }),
                    value: Box::new(Type::Str),
                };
                self.validate_dict_const_keys(&arg.value, &expected_ty)?;
            }
            return Ok(Type::Str);
        }
        // Fall back to Phase 1 approach for backwards compat
        if let Some(const_keys) = self.get_fstring_keys_from_expr(receiver) {
            // ... same as Phase 1
        }
    }
}
```

### Step 2.3: Runtime Implementation

Implement `FString.with()` in interpreter:

```rust
// In src/rust/runtime/src/value.rs or interpreter
impl RuntimeValue {
    fn fstring_with(&self, data: &HashMap<String, String>) -> String {
        let mut result = self.template.clone();
        for (key, value) in data {
            result = result.replace(&format!("{{{}}}", key), value);
        }
        result
    }
}
```

**Files to modify:**
- `src/rust/runtime/src/value.rs` - Add FString.with
- `src/app/interpreter/` - Handle .with method

### Step 2.4: Deprecate Explicit Syntax (Optional)

After `.with` is stable, consider deprecating:
```simple
# Deprecated (still works but shows warning)
val data: Dict<template.keys, String> = {...}

# Preferred
val result = template.with {...}
```

### Phase 2 File Summary

| File | Changes |
|------|---------|
| `src/rust/type/src/lib.rs` | Add `Type::FString` variant |
| `src/rust/type/src/checker_infer.rs` | FString inference, update .with |
| `src/rust/type/src/checker_unify.rs` | FString unification |
| `src/rust/runtime/src/value.rs` | Runtime .with implementation |
| `src/app/interpreter/expr/calls.rs` | Interpreter .with support |

## Testing Plan

### Unit Tests
```rust
#[test]
fn test_fstring_with_valid_keys() {
    let code = r#"
        val t = "Hello {name}"
        val r = t.with {"name": "Alice"}
    "#;
    assert!(type_check(code).is_ok());
}

#[test]
fn test_fstring_with_invalid_key() {
    let code = r#"
        val t = "Hello {name}"
        val r = t.with {"nam": "Alice"}
    "#;
    assert!(type_check(code).is_err());
}
```

### Integration Tests
```simple
# test/features/fstring_with_spec.spl
describe "FString.with":
    it "formats with valid keys":
        val template = "Hello {name}!"
        val result = template.with {"name": "World"}
        expect result to_equal "Hello World!"

    it "catches invalid keys at compile time":
        # This should not compile
        # val bad = "Hi {x}".with {"y": "z"}
        pass
```

## Rollout Strategy

1. **Phase A:** Implement Type::FString (no breaking changes)
2. **Phase B:** Implement .with method (additive)
3. **Phase C:** Add deprecation warnings for old syntax (optional)
4. **Phase D:** Remove old syntax in v2.0 (breaking, optional)

## Backward Compatibility

- Current explicit syntax continues to work
- `.with` is purely additive
- No breaking changes required

---

## Implementation Status (2026-01-21)

### Phase 1: Complete ✓
- `.with` validation for FString literals and local variables
- `get_fstring_keys_from_expr()` helper for expression-based key extraction
- FString placeholder tolerance (undefined identifiers allowed)

### Phase 2: Complete ✓
- `Type::FString { const_keys }` variant added to type system
- FString inference returns `Type::FString` (not just `Type::Str`)
- FString/Str unification for backwards compatibility
- `.with` handler uses type system (with Phase 1 fallback)

### Tests: 15 passing
- `test_fstring_with_literal_valid_keys`
- `test_fstring_with_variable_valid_keys`
- `test_fstring_with_invalid_key`
- `test_fstring_with_missing_key`
- `test_fstring_with_multiple_placeholders`
- `test_fstring_type_inference`
- `test_fstring_unification_with_str`

### Remaining (Optional)
- Runtime `.with` implementation (interpreter/codegen)
- Deprecation warnings for old explicit syntax
