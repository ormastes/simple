# No-Parentheses Function Calls Specification
*Source:* `test/feature/usage/no_paren_calls_spec.spl`
**Feature IDs:** #300-310  |  **Category:** Syntax  |  **Status:** Implemented

## Overview




## Overview

No-parentheses function calls allow calling functions without wrapping arguments in parentheses,
providing Ruby-style syntax for cleaner, more readable code. This feature supports simple function
calls, trailing lambdas, colon-blocks, and works with identifiers, field access, and path expressions.

## Syntax

### Basic No-Paren Calls

```simple
print "Hello"              # print("Hello")
val result = add 2, 3      # val result = add(2, 3)
```

### With Field Access

```simple
obj.method arg             # obj.method(arg)
```

### With Trailing Lambdas

```simple
map numbers \x: x * 2      # map(numbers, \x: x * 2)
```

### With Colon-Blocks

```simple
describe "Feature":
    test code
# describe("Feature", fn(): test code)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| No-Paren Call | Function call without wrapping arguments in `()` |
| Callable Expression | Identifier, field access, or path that can be called |
| Trailing Lambda | Lambda with `\` syntax as final argument |
| Colon-Block | Indented block after `:` becomes lambda argument |
| Comma Required | Arguments must be separated by commas in Normal mode |

## Behavior

- **Callable expressions**: Only identifiers, field access (`obj.method`), and paths (`Module.func`)
- **Comma-separated**: Multiple arguments require commas in Normal mode
- **Trailing lambda**: Backslash syntax (`\params: body`) can append lambda
- **Colon-block**: `:` followed by indent creates lambda argument
- **No nesting**: Strict mode disallows nested no-paren calls
- **Statement level**: Works at statement level, not within complex expressions

## Related Specifications

- [Trailing Blocks](../trailing_blocks/trailing_blocks_spec.md) - Lambda syntax with backslash
- [Functions](../functions/functions_spec.md) - Function definition and calling
- [Lambdas/Closures](../lambdas_closures/lambdas_closures_spec.md) - Lambda expressions

## Implementation Notes

**Parser:** `src/parser/src/expressions/no_paren.rs`
- `parse_with_no_paren_calls()` - Main entry point
- `is_callable_expr()` - Determines if expression can start no-paren call
- `can_start_argument()` - Checks if token can begin an argument

**Modes:**
- **Normal**: Default, allows nesting (may be ambiguous)
- **Strict**: GPU mode, disallows nested no-paren calls

**Performance:** No-paren calls desugar to regular calls during parsing - zero runtime overhead.

## Examples

```simple
# Basic calls
print "Hello World"
val sum = add 5, 10

# With field access
list.each item

# With trailing lambda
map items \x: x * 2
filter values \v: v > 0

# With colon-block
describe "Test":
    it "works":
        expect(true).to_equal(true)

# Multiple arguments
call arg1, arg2, arg3
```

## Feature: No-Paren Calls - Basic Syntax

## Basic No-Paren Call Syntax

    Functions can be called without parentheses, with arguments separated by commas.

### Scenario: with single argument

### Scenario: Single Argument

        Function with one argument can omit parentheses.

        ```simple
        fn double(x):
            x * 2

        val result = double 5  # double(5)
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | calls function with single argument | pass |
| 2 | calls with literal argument | pass |
| 3 | calls with identifier argument | pass |

**Example:** calls function with single argument
    Given val result = double 5
    Then  expect(result).to_equal(10)

**Example:** calls with literal argument
    Given val result = identity 42
    Then  expect(result).to_equal(42)

**Example:** calls with identifier argument
    Given val value = 100
    Given val result = identity value
    Then  expect(result).to_equal(100)

### Scenario: with multiple arguments

### Scenario: Multiple Arguments

        Multiple arguments require comma separation.

        ```simple
        fn add(a, b):
            a + b

        val sum = add 10, 20  # add(10, 20)
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | calls with two arguments | pass |
| 2 | calls with three arguments | pass |
| 3 | mixes literals and identifiers | pass |

**Example:** calls with two arguments
    Given val result = add(10, 20)
    Then  expect(result).to_equal(30)

**Example:** calls with three arguments
    Given val result = add3(5, 10, 15)
    Then  expect(result).to_equal(30)

**Example:** mixes literals and identifiers
    Given val factor = 5
    Given val result = multiply(factor, 3)
    Then  expect(result).to_equal(15)

## Feature: No-Paren Calls - Argument Types

## Different Argument Types

    No-paren calls support various argument types: literals, identifiers, expressions.

### Scenario: with literals

### Scenario: Literal Arguments

        Integer, float, string, and boolean literals as arguments.

        ```simple
        func 42                 # Integer
        func 3.14               # Float
        func "text"             # String
        func true               # Boolean
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | passes integer literal | pass |
| 2 | passes string literal | pass |
| 3 | passes boolean literal | pass |

**Example:** passes integer literal
    Given val result = identity 42
    Then  expect(result).to_equal(42)

**Example:** passes string literal
    Given val result = identity "hello"
    Then  expect(result).to_equal("hello")

**Example:** passes boolean literal
    Given val result = identity true
    Then  expect(result).to_equal(true)

### Scenario: with parenthesized expressions

### Scenario: Parenthesized Expressions

        Complex expressions can be wrapped in parentheses.

        ```simple
        func (a + b), (c * d)
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | passes arithmetic expression | pass |
| 2 | passes multiple expressions | pass |

**Example:** passes arithmetic expression
    Given val result = square (3 + 2)
    Then  expect(result).to_equal(25)

**Example:** passes multiple expressions
    Given val result = add((2 * 3), (4 + 5))
    Then  expect(result).to_equal(15)

## Feature: No-Paren Calls - Nested Calls

## Nested Function Calls

    Mixing parenthesized and no-paren calls.

### Scenario: with inner parenthesized calls

### Scenario: Inner Calls with Parens

        Inner calls use parentheses, outer call uses no-paren syntax.

        ```simple
        outer inner(arg)
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | nests parenthesized call | pass |
| 2 | chains multiple functions | pass |

**Example:** nests parenthesized call
    Given val result = double triple(5)
    Then  expect(result).to_equal(30)

**Example:** chains multiple functions
    Given val result = add1 add2(10)
    Then  expect(result).to_equal(13)

## Feature: No-Paren Calls - Trailing Lambdas

## Trailing Lambdas with No-Paren Calls

    Lambda with backslash syntax can be the final argument.

### Scenario: with single argument plus lambda

### Scenario: Argument Plus Trailing Lambda

        Combine regular argument with trailing lambda.

        ```simple
        map array \x: x * 2
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | accepts trailing lambda | pass |
| 2 | passes multiple args plus lambda | pass |

**Example:** accepts trailing lambda
    Given val result = apply 5 {NL}: n * 2
    Then  expect(result).to_equal(10)

**Example:** passes multiple args plus lambda
    Given var acc = init
    Given var i = 0
    Given val nums = [1, 2, 3]
    Given val sum = fold(nums, 0) \acc, x: acc + x
    Then  expect(sum).to_equal(6)

## Feature: No-Paren Calls - Method Calls

## Method Calls with No-Paren Syntax

    Methods accessed via field access can use no-paren syntax.

### Scenario: with method calls

### Scenario: Method Call Syntax

        Methods can be called without parentheses.

        ```simple
        obj.method arg
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | uses no-paren with helper function | pass |

**Example:** uses no-paren with helper function
    Given val double_func = get_double_func()
    Given val result = double_func 21
    Then  expect(result).to_equal(42)

## Feature: No-Paren Calls - Context

## Statement vs Expression Context

    No-paren calls work at statement level and in assignments.

### Scenario: in assignments

### Scenario: Assignment Context

        No-paren calls on right side of assignments.

        ```simple
        val result = func arg
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | works in val assignments | pass |
| 2 | works in var assignments | pass |

**Example:** works in val assignments
    Given val result = double 10
    Then  expect(result).to_equal(20)

**Example:** works in var assignments
    Given var result = add(5, 7)
    Then  expect(result).to_equal(12)

### Scenario: in return statements

### Scenario: Return Statement Context

        No-paren calls in return expressions.

        ```simple
        fn wrapper(x):
            double x
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | works in implicit returns | pass |

**Example:** works in implicit returns
    Given val result = wrapper 7
    Then  expect(result).to_equal(14)

## Feature: No-Paren Calls - String Arguments

## String Literal Arguments

    String literals work naturally with no-paren syntax.

### Scenario: with string literals

### Scenario: String Literals

        Pass strings without parentheses.

        ```simple
        print "Hello World"
        greet "Alice"
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | passes single string | pass |
| 2 | passes string with spaces | pass |

**Example:** passes single string
    Given val result = identity "test"
    Then  expect(result).to_equal("test")

**Example:** passes string with spaces
    Given val result = identity "hello world"
    Then  expect(result).to_equal("hello world")

## Feature: No-Paren Calls - Mixed Syntax

## Mixing Paren and No-Paren Calls

    Combine both calling styles as needed.

### Scenario: with mixed styles

### Scenario: Mixed Call Styles

        Some calls with parens, some without.

        ```simple
        outer inner(x), arg2
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | mixes paren and no-paren | pass |
| 2 | chains multiple mixed calls | pass |

**Example:** mixes paren and no-paren
    Given val result = add(double(5), 3)
    Then  expect(result).to_equal(13)

**Example:** chains multiple mixed calls
    Given val result = add1 add2(add3(10))
    Then  expect(result).to_equal(16)

## Feature: No-Paren Calls - Edge Cases

## Edge Case Handling

    Special cases and boundary conditions.

### Scenario: with zero arguments

### Scenario: Zero Arguments

        Functions with no arguments require parentheses.

        ```simple
        func()  # Parentheses required for zero args
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | requires parens for zero args | pass |

**Example:** requires parens for zero args
    Given val result = get_value()
    Then  expect(result).to_equal(42)

### Scenario: with single identifier

### Scenario: Single Identifier Argument

        Passing a single variable.

| # | Example | Status |
|---|---------|--------|
| 1 | passes single variable | pass |

**Example:** passes single variable
    Given val num = 7
    Given val result = square num
    Then  expect(result).to_equal(49)


