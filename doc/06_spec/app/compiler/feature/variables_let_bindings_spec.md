# Variables and Bindings Specification

**Feature ID:** #1050 | **Category:** Language | **Status:** Implemented

_Source: `test/feature/usage/variables_let_bindings_spec.spl`_

---

## Overview

Tests for variable declarations including val (immutable) and var (mutable)
bindings, type inference, and scoping rules.

## Syntax

```simple
# Immutable binding (preferred)
val name = "Alice"

# Mutable binding
var count = 0
count = count + 1

# Tuple destructuring
var (a, b) = (1, 2)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| val | Immutable binding - cannot be reassigned |
| var | Mutable binding - can be reassigned |

## Deprecated

- `let` - Use `val` instead
- `let mut` - Use `var` instead

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 23 |

## Test Structure

### Variables and Bindings

#### val bindings

- ✅ creates immutable binding
- ✅ allows shadowing with new val
- ✅ binds expression results
- ✅ binds complex expressions
#### var bindings

- ✅ creates mutable binding
- ✅ allows multiple reassignments
### Scoping and Nesting

#### nested scopes

- ✅ inner scope shadows outer
- ✅ inner scope can read outer
#### loop scoping

- ✅ loop variable isolated to loop
### Additional val/var Patterns

#### val with different types

- ✅ creates immutable boolean
- ✅ creates immutable float
#### var initialization patterns

- ✅ initializes var with expression
- ✅ modifies var in loop
### Tuple Destructuring Bindings

#### var with tuples

- ✅ destructures tuple into mutable bindings
#### val with tuples

- ✅ destructures tuple into immutable bindings
### Type Inference

#### primitive type inference

- ✅ infers integer type
- ✅ infers string type
- ✅ infers array type
### Global Functions with Bindings

#### len function

- ✅ gets length of array
- ✅ gets length using method syntax
### Option Type Bindings

#### Some bindings

- ✅ binds Some value
- ✅ unwraps Some value
#### None bindings

- ✅ binds None value

