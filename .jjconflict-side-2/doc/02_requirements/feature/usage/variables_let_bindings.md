# Variables and Bindings Specification
*Source:* `test/feature/usage/variables_let_bindings_spec.spl`
**Feature IDs:** #1050  |  **Category:** Language  |  **Status:** Implemented

## Overview



use std.text.{NL}

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

## Feature: Variables and Bindings

## Variable Declaration Support

    Verifies val/var declarations, type inference, mutability rules,
    and proper scoping behavior.

### Scenario: val bindings

### Scenario: Immutable Bindings

        Tests for val keyword creating immutable bindings.

| # | Example | Status |
|---|---------|--------|
| 1 | creates immutable binding | pass |
| 2 | allows shadowing with new val | pass |
| 3 | binds expression results | pass |
| 4 | binds complex expressions | pass |

**Example:** creates immutable binding
    Given val x = 42
    Then  expect x == 42

**Example:** allows shadowing with new val
    Given val x = 1
    Given val x = 2
    Then  expect x == 2

**Example:** binds expression results
    Given val result = 10 + 20 * 2
    Then  expect result == 50

**Example:** binds complex expressions
    Given val result = (5 + 3) * 4 - 10 / 2
    Then  expect result == 27

### Scenario: var bindings

### Scenario: Mutable Bindings

        Tests for var keyword creating mutable bindings.

| # | Example | Status |
|---|---------|--------|
| 1 | creates mutable binding | pass |
| 2 | allows multiple reassignments | pass |

**Example:** creates mutable binding
    Given var x = 0
    Then  expect x == 10

**Example:** allows multiple reassignments
    Given var x = 1
    Then  expect x == 3

## Feature: Scoping and Nesting

## Variable Scoping Behavior

    Tests for variable scoping with nested blocks.

### Scenario: nested scopes

### Scenario: Block Scoping

        Tests that inner scope can shadow outer variables.

| # | Example | Status |
|---|---------|--------|
| 1 | inner scope shadows outer | pass |
| 2 | inner scope can read outer | pass |

**Example:** inner scope shadows outer
    Given val x = 1
    Given val x = 2
    Then  expect x == 2
    Then  expect x == 1

**Example:** inner scope can read outer
    Given val x = 10
    Given var result = 0
    Then  expect result == 15

### Scenario: loop scoping

### Scenario: Loop Variable Scope

        Tests that loop variables are properly scoped.

| # | Example | Status |
|---|---------|--------|
| 1 | loop variable isolated to loop | pass |

**Example:** loop variable isolated to loop
    Given val i = 100
    Given var sum = 0
    Then  expect i == 100
    Then  expect sum == 10

## Feature: Additional val/var Patterns

## More Binding Patterns

    Tests for additional val/var usage patterns.

### Scenario: val with different types

### Scenario: Immutable Different Types

        Tests val bindings with various types.

| # | Example | Status |
|---|---------|--------|
| 1 | creates immutable boolean | pass |
| 2 | creates immutable float | pass |

**Example:** creates immutable boolean
    Given val flag = true
    Then  expect flag == true

**Example:** creates immutable float
    Given val pi = 3.14
    Then  expect pi > 3.0

### Scenario: var initialization patterns

### Scenario: Mutable Initialization

        Tests var initialization and modification.

| # | Example | Status |
|---|---------|--------|
| 1 | initializes var with expression | pass |
| 2 | modifies var in loop | pass |

**Example:** initializes var with expression
    Given var x = 5 * 2
    Then  expect x == 20

**Example:** modifies var in loop
    Given var sum = 0
    Then  expect sum == 6

## Feature: Tuple Destructuring Bindings

## Destructuring in Bindings

    Tests for tuple destructuring in variable declarations.

### Scenario: var with tuples

### Scenario: Mutable Tuple Destructuring

        Tests for destructuring tuples with mutable bindings.

| # | Example | Status |
|---|---------|--------|
| 1 | destructures tuple into mutable bindings | pass |

**Example:** destructures tuple into mutable bindings
    Given var (a, b) = (1, 2)
    Then  expect a + b == 30

### Scenario: val with tuples

### Scenario: Immutable Tuple Destructuring

        Tests for destructuring tuples with immutable bindings.

| # | Example | Status |
|---|---------|--------|
| 1 | destructures tuple into immutable bindings | pass |

**Example:** destructures tuple into immutable bindings
    Given val (x, y) = (3, 4)
    Then  expect x + y == 7

## Feature: Type Inference

## Automatic Type Deduction

    Tests for type inference on variable bindings.

### Scenario: primitive type inference

### Scenario: Infer Primitive Types

        Tests that primitive types are inferred correctly.

| # | Example | Status |
|---|---------|--------|
| 1 | infers integer type | pass |
| 2 | infers string type | pass |
| 3 | infers array type | pass |

**Example:** infers integer type
    Given val x = 42
    Then  expect x + 8 == 50

**Example:** infers string type
    Given val s = "hello"
    Then  expect s.len() == 5

**Example:** infers array type
    Given val arr = [1, 2, 3]
    Then  expect arr.len() == 3

## Feature: Global Functions with Bindings

## Built-in Functions

    Tests for global functions like len() working with bindings.

### Scenario: len function

### Scenario: Length of Collections

        Tests the global len() function with arrays.

| # | Example | Status |
|---|---------|--------|
| 1 | gets length of array | pass |
| 2 | gets length using method syntax | pass |

**Example:** gets length of array
    Given val arr = [1, 2, 3, 4, 5]
    Then  expect len(arr) == 5

**Example:** gets length using method syntax
    Given val arr = [1, 2, 3]
    Then  expect arr.len() == 3

## Feature: Option Type Bindings

## Option Types

    Tests for binding Option values (Some and None).

### Scenario: Some bindings

### Scenario: Some Value Binding

        Tests binding Some values.

| # | Example | Status |
|---|---------|--------|
| 1 | binds Some value | pass |
| 2 | unwraps Some value | pass |

**Example:** binds Some value
    Given val opt: Option<i64> = Some(42)
    Then  expect opt.?

**Example:** unwraps Some value
    Given val opt: Option<i64> = Some(99)
    Then  expect opt.unwrap() == 99

### Scenario: None bindings

### Scenario: None Value Binding

        Tests binding None values.

| # | Example | Status |
|---|---------|--------|
| 1 | binds None value | pass |

**Example:** binds None value
    Given val opt: Option<i64> = None
    Then  expect not opt.?


