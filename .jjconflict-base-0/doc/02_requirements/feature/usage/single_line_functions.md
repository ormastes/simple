# Single-Line Function Definitions Specification
*Source:* `test/feature/usage/single_line_functions_spec.spl`
**Feature IDs:** #SYNTAX-INLINE  |  **Category:** Syntax  |  **Status:** Implemented

## Overview



Single-line (inline) function definitions allow functions to be defined with
an implicit return expression on the same line as the function signature.
The syntax replaces the indented block with an expression that is automatically
returned.

## Syntax

```simple
fn name(): implicit_return_expr
fn name(param: Type) -> ReturnType: expr
```

## Key Behaviors

- Single-line functions have an implicit return expression (no explicit `return` needed)
- The expression is evaluated and returned automatically
- Explicit return types are optional but supported
- Works with zero, one, or multiple parameters
- Compatible with class methods and static functions
- Traditional block syntax is still supported and can be mixed in the same file

## Feature: Single-Line Function Definitions

Verifies that inline expression body syntax works correctly for function
    definitions. Tests cover basic single-line syntax, return types,
    method definitions, and interaction with traditional block syntax.

### Scenario: basic syntax

| # | Example | Status |
|---|---------|--------|
| 1 | parses inline expression body | pass |
| 2 | parses with multiple parameters | pass |
| 3 | parses with no parameters | pass |
| 4 | handles complex expressions | pass |
| 5 | returns immediately without explicit return | pass |

**Example:** parses inline expression body
    Then  expect double(5) == 10

**Example:** parses with multiple parameters
    Then  expect add(3, 4) == 7

**Example:** parses with no parameters
    Then  expect get_answer() == 42

**Example:** handles complex expressions
    Then  expect complex(10) == 25

**Example:** returns immediately without explicit return
    Then  expect square(4) == 16

### Scenario: with explicit return types

| # | Example | Status |
|---|---------|--------|
| 1 | supports explicit return type annotation | pass |
| 2 | works with function parameter types | pass |
| 3 | infers return type from expression | pass |

**Example:** supports explicit return type annotation
    Then  expect typed_double(5) == 10

**Example:** works with function parameter types
    Then  expect typed_add(10, 20) == 30

**Example:** infers return type from expression
    Then  expect inferred(41) == 42

### Scenario: with method definitions

| # | Example | Status |
|---|---------|--------|
| 1 | works with class methods | pass |
| 2 | works with mutable methods | pass |
| 3 | works with static functions | pass |

**Example:** works with class methods
    Given val c = Counter(count: 42)
    Then  expect c.get_count() == 42

**Example:** works with mutable methods
    Given val acc = Accumulator(total: 0)
    Then  expect acc.total == 15

**Example:** works with static functions
    Then  expect MathHelper.pi_approximation() == 3.14159

### Scenario: with collection operations

| # | Example | Status |
|---|---------|--------|
| 1 | works with lambda-like expressions | pass |
| 2 | handles filtering in single line | pass |

**Example:** works with lambda-like expressions
    Then  expect twice_each([1, 2, 3]) == [2, 4, 6]

**Example:** handles filtering in single line
    Then  expect evens_only([1, 2, 3, 4, 5]) == [2, 4]

### Scenario: mixing with block syntax

| # | Example | Status |
|---|---------|--------|
| 1 | can coexist with traditional block functions | pass |
| 2 | block functions still work normally | pass |
| 3 | allows either style in same module | pass |

**Example:** can coexist with traditional block functions
    Given val doubled = inline(x)
    Then  expect block(5) == 11

**Example:** block functions still work normally
    Given val y = x * 2
    Then  expect block_complex(5) == 11

**Example:** allows either style in same module
    Then  expect style1(10) == 11
    Then  expect style2(10) == 12

### Scenario: edge cases

| # | Example | Status |
|---|---------|--------|
| 1 | works with nested function calls | pass |
| 2 | handles string expressions | pass |
| 3 | works with conditional expressions | pass |

**Example:** works with nested function calls
    Then  expect outer(5) == 11

**Example:** handles string expressions
    Then  expect greeting("World") == "Hello, World!"

**Example:** works with conditional expressions
    Then  expect max_of_two(10, 5) == 10
    Then  expect max_of_two(3, 8) == 8


