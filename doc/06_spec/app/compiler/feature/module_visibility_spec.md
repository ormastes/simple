# Module Visibility Specification

**Feature ID:** #LANG-042 (Feature DB ID: 300) | **Category:** Language | **Difficulty:** 3/5 | **Status:** In Progress (Core Complete, Integration Pending)

_Source: `test/feature/usage/module_visibility_spec.spl`_

---

## Overview

Module visibility system with filename-based auto-public rule. Types matching
the filename are automatically public; all other declarations are private by
default unless explicitly marked with `public`.

This enables top-level `val` declarations (private by default) and provides
clear visibility control for APIs.

## Syntax

```simple
# file: test_case.spl

# Auto-public: name matches filename (snake_case -> PascalCase)
class TestCase:
    id: i32

# Private by default (name doesn't match)
class Helper:
    data: i32

# Explicit public
public class PublicHelper:
    data: i32

# Top-level val (private by default)
val CONSTANT: i32 = 42

# Explicit public constant
public val PUBLIC_CONSTANT: i32 = 100

# Private function (default)
fn helper_fn(): pass

# Public function (explicit)
public fn public_fn(): pass
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Filename Match | Type name matching filename is auto-public |
| Private Default | All other declarations are private by default |
| `public` Keyword | Explicitly marks declaration as public |
| `private` Keyword | Explicitly marks declaration as private (optional) |
| Top-level `val` | Module-level constants, private by default |
| Name Conversion | snake_case filename -> PascalCase type |

## Behavior

- `test_case.spl` -> `class TestCase` is auto-public
- Other classes/structs in file are private by default
- Functions are private by default
- Top-level `val`/`var` are private by default
- Use `public` keyword to export additional items
- `mod.spl` files are for re-exports only (no auto-public type)

## Related Specifications

- Module System - Import/export mechanics
- Type System - Type visibility in type checking
- Code Quality Tools - Visibility linting

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 26 |

## Test Structure

### Module Visibility Filename Match

- ✅ auto-publics class matching filename
- ✅ converts snake_case filename to PascalCase
- ✅ makes non-matching types private by default
### Module Visibility Keywords

- ✅ supports public keyword for classes
- ✅ supports public keyword for functions
- ✅ supports private keyword (explicit)
- ✅ allows redundant private on non-matching types
### Module Visibility Top-Level Val

- ✅ allows private top-level val
- ✅ allows public top-level val
- ✅ allows top-level val in expressions
- ✅ rejects mutable top-level var without explicit public
### Module Visibility Impl Blocks

- ✅ methods on public type are public by default
- ✅ methods on private type are private
- ✅ allows private methods on public type
### Module Visibility Diagnostics

- ✅ warns on implicitly public non-matching type (phase 1)
- ✅ warns on implicitly public function (phase 1)
- ✅ errors on accessing private type (phase 2)
- ✅ suggests adding public modifier in warning
### Module Visibility Re-exports

- ✅ mod.spl has no auto-public type
### Module Visibility Import Integration

- ✅ allows importing public items
- ✅ rejects importing private items
- ✅ allows qualified access to public items
### Module Visibility Edge Cases

- ✅ handles multiple types with same prefix
- ✅ handles single-word filenames
- ✅ handles acronyms in filenames
- ✅ handles nested types visibility

