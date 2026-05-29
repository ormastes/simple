# Alias and Deprecated Feature Specification

**Feature ID:** #ALIAS-001 to #ALIAS-010 | **Category:** Language | Syntax | **Difficulty:** 2/5 | **Status:** In Progress

_Source: `test/feature/usage/alias_deprecated_spec.spl`_

---

## Overview

This specification covers the alias and deprecation features:
1. Type alias: `alias NewName = OldName` for classes/structs/enums
2. Function alias: `fn new_name = old_name` for functions and methods
3. @deprecated decorator with enforcement and suggestions

## Syntax

```simple
# Type alias
alias Point2D = Point
alias Optional = Option

# Function alias
fn println = print
fn each = iter

# Deprecation with suggestion
@deprecated("Use println instead")
fn print(msg):
    ...

# Chained aliases
impl List:
    fn each = iter
    fn forEach = each
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Type Alias | Creates a new name for an existing class/struct/enum |
| Function Alias | Creates a new name for an existing function |
| @deprecated | Marks an item as deprecated with optional message |
| Suggestion | Non-deprecated alternative suggested in warnings |

## Behavior

- Aliases create direct mappings, not new types
- Deprecated items produce warnings when used
- Warnings include suggestions for non-deprecated alternatives
- Alias chains are resolved correctly (A -> B -> C)

## Related Specifications

- [Type Alias](type_alias_spec.spl) - Original `type` keyword alias

## Implementation Notes

The alias feature is implemented at the parser and HIR lowering levels.
Deprecation warnings are collected during lowering and reported after compilation.

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 56 |

## Test Structure

### Type Alias Parsing

- ✅ parses simple type alias
- ✅ parses type alias with uppercase names
### Function Alias Parsing

- ✅ parses function alias
- ✅ parses function alias with lowercase names
### Deprecation Decorator

- ✅ parses deprecated decorator without message
- ✅ parses deprecated decorator with message
### Alias Resolution

- ✅ resolves type alias to original type
- ✅ resolves function alias to original function
- ✅ resolves chained aliases
### Deprecation Warnings

- ✅ generates warning for deprecated function usage
- ✅ includes deprecation message in warning
- ✅ suggests non-deprecated alternative
### Alias Integration

- ✅ supports library migration pattern
- ✅ supports method aliasing in impl blocks
### Type Alias Edge Cases

- ✅ rejects self-referential alias
- ✅ rejects alias to non-existent type
- ✅ rejects duplicate alias names

