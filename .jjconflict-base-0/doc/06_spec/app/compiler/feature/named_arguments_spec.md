# Named Arguments Specification

**Feature ID:** #NAMED-ARGS-001 | **Category:** Language | Functions | **Status:** Implemented

_Source: `test/feature/usage/named_arguments_spec.spl`_

---

## Overview

Tests for named argument support allowing function calls with explicit
parameter names, improving code clarity and enabling flexible argument ordering.

## Syntax

```simple
fn create_user(name: str, email: str, age: i64) -> User:
    User(name: name, email: email, age: age)

# Call with positional arguments
val user1 = create_user("Alice", "alice@example.com", 30)

# Call with named arguments
val user2 = create_user(age=25, name="Bob", email="bob@example.com")

# Mixed positional and named
val user3 = create_user("Charlie", email="charlie@example.com", age=35)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Named Argument | Explicitly passing parameter by name |
| Positional Argument | Passing argument by position order |
| Argument Reordering | Non-positional order with named arguments |
| Default Values | Optional parameters with defaults |
| Clarity | Improved code readability with explicit parameter names |

## Behavior

- Named arguments can be passed in any order
- Positional arguments must precede named arguments (if mixed)
- Parameter names are part of the function signature
- Type checking applies to named arguments like positional
- Named arguments cannot be repeated in a single call
- Works with constructors and regular functions

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 17 |

## Test Structure

### Named Arguments Basic Usage

- ✅ calls function with named arguments
- ✅ passes values correctly with named arguments
- ✅ works with string values
### Named Arguments Reordering

- ✅ allows reversed argument order
- ✅ reorders three arguments
- ✅ reorders with different calculation
### Mixed Positional and Named Arguments

- ✅ mixes positional and named arguments
- ✅ uses positional first then named
- ✅ uses single positional with multiple named
### Named Arguments with Defaults

- ✅ uses default when argument not provided
- ✅ overrides default with named argument
- ✅ works with multiple defaults
### Named Arguments in Methods

- ✅ uses named arguments with class methods
- ✅ reorders method arguments
### Named Arguments Edge Cases

- ✅ handles single named argument
- ✅ handles many named arguments
- ✅ works with nested function calls

