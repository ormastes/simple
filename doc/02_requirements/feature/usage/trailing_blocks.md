# Trailing Blocks Specification
*Source:* `test/feature/usage/trailing_blocks_spec.spl`
**Feature IDs:** #450  |  **Category:** Syntax  |  **Status:** Implemented

## Overview


use std.text.{NL}

## Overview

Trailing blocks (also called "trailing lambdas") provide Ruby-style syntax for passing
lambda functions as the last argument to a function or method. They use a backslash (`\`)
to introduce parameters, making functional-style code more readable and enabling DSL-like
syntax patterns.

## Syntax

### Basic Trailing Block

```simple
# Traditional lambda syntax
items.map(\x: x * 2)

# Trailing block syntax (cleaner)
items.map \x: x * 2
```

### With Multiple Parameters

```simple
items.reduce(0) \acc, x: acc + x
```

### Block Bodies

```simple
items.each \item:
    print(item)
    process(item)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Trailing Lambda | Lambda passed as last argument using `\` syntax |
| Backslash Syntax | `\params: body` introduces a trailing block |
| Method Chaining | Trailing blocks work naturally with method chains |
| DSL Support | Enable Ruby-style domain-specific languages |

## Behavior

- **Trailing blocks** are parsed as the last argument to a function/method call
- **Backslash syntax** (`\`) immediately signals a lambda, enabling LL(1) parsing
- **Inline expressions** can be used for simple one-liners: `\x: x * 2`
- **Block bodies** with indentation allow multi-statement blocks
- **Multiple parameters** are comma-separated: `\x, y, z: body`
- **Zero parameters** use empty parameter list: `\: body`
- Works with both **parenthesized** and **no-parentheses** calls

## Related Specifications

- [Lambdas/Closures](../lambdas_closures/lambdas_closures_spec.md) - Lambda syntax and closure semantics
- [No-Parentheses Calls](../no_paren_calls/no_paren_calls_spec.md) - Calling functions without parens
- [Functional Update](../functional_update/functional_update_spec.md) - Functional transformation patterns

## Implementation Notes

**Parser:** `src/parser/src/expressions/postfix.rs`
- `parse_trailing_lambda()` (lines 345-372): Parses trailing block syntax
- `parse_lambda_params()` (lines 377-396): Parses parameter lists

**Integration Points:**
- Function calls with parentheses (line 328-333)
- Method calls with parentheses (line 158-164)
- Method calls without parentheses (line 170-180)
- No-parentheses function calls

**Performance:** Trailing blocks are syntactic sugar - no runtime overhead compared to
traditional lambda syntax. They parse in O(1) time after detecting the backslash token.

## Examples

```simple
# Functional operations
val doubled = [1, 2, 3].map \x: x * 2
val positives = numbers.filter \x: x > 0

# DSL-style router
router.get "/hello" \: "Hello World"
router.post "/user" \request: process(request)

# Method chaining
items.filter \x: x > 0
     .map \x: x * 2
     .each \x: print(x)
```

## Feature: Trailing Blocks - Basic Syntax

## Basic Trailing Block Syntax

    Trailing blocks use backslash (`\`) to introduce lambda parameters,
    allowing cleaner syntax when passing functions as arguments.

### Scenario: with single parameter

### Scenario: Single Parameter Trailing Block

        A trailing block with one parameter uses `\param: expr` syntax.

        ```simple
        val doubled = map([1, 2, 3]) \x: x * 2
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | passes trailing block to function | pass |
| 2 | works with method-style calls | pass |

**Example:** passes trailing block to function
    Given val result = apply(5) {NL}: n * 2
    Then  expect(result).to_equal(10)

**Example:** works with method-style calls
    Given var result = []
    Given var i = 0
    Given val nums = [1, 2, 3]
    Given val doubled = double_each(nums) \x: x * 2
    Then  expect(doubled[0]).to_equal(2)
    Then  expect(doubled[1]).to_equal(4)
    Then  expect(doubled[2]).to_equal(6)

### Scenario: with multiple parameters

### Scenario: Multiple Parameters

        Trailing blocks support multiple comma-separated parameters.

        ```simple
        reduce(items, 0) \acc, x: acc + x
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | accepts multiple parameters | pass |
| 2 | works with three parameters | pass |

**Example:** accepts multiple parameters
    Given var acc = init
    Given var i = 0
    Given val nums = [1, 2, 3, 4]
    Given val sum = fold(nums, 0) \acc, x: acc + x
    Then  expect(sum).to_equal(10)

**Example:** works with three parameters
    Given var acc = init
    Given var i = 0
    Given val letters = ["a", "b", "c"]
    Given val result = fold3(letters, "") \acc, item, idx: acc + item
    Then  expect(result).to_equal("abc")

### Scenario: with zero parameters

### Scenario: Zero Parameters

        Trailing blocks can have no parameters using `\:` syntax.

        ```simple
        router.get "/health" \: "ok"
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | allows zero-parameter blocks | pass |
| 2 | useful for constant responses | pass |

**Example:** allows zero-parameter blocks
    Given val result = call_block \: 42
    Then  expect(result).to_equal(42)

**Example:** useful for constant responses
    Given val response = get_handler("/health") \: "ok"
    Then  expect(response).to_equal("ok")

## Feature: Trailing Blocks - Expression Forms

## Inline Expressions vs Block Bodies

    Trailing blocks support both inline expressions (single-line) and
    indented block bodies (multi-statement).

### Scenario: with inline expressions

### Scenario: Inline Expressions

        Simple expressions can be written inline after the colon.

        ```simple
        items.map \x: x * 2
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | evaluates inline expression | pass |
| 2 | supports arithmetic expressions | pass |

**Example:** evaluates inline expression
    Given val result = transform(10) {NL}: n + 5
    Then  expect(result).to_equal(15)

**Example:** supports arithmetic expressions
    Given val sum = compute(3, 4) \x, y: x + y
    Then  expect(sum).to_equal(7)
    Given val product = compute(3, 4) \x, y: x * y
    Then  expect(product).to_equal(12)

### Scenario: with block bodies

### Scenario: Block Bodies

        Multi-statement blocks use indentation like regular blocks.

        ```simple
        items.each \item:
            print(item)
            process(item)
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | can use traditional lambdas for multi-statement logic | pass |
| 2 | can compute complex expressions inline | pass |

**Example:** can use traditional lambdas for multi-statement logic
    Given var result = run_block(\: 42)
    Then  expect(result).to_equal(42)

**Example:** can compute complex expressions inline
    Given val result = process(5) {NL}: (n * 2) + 3
    Then  expect(result).to_equal(13)

## Feature: Trailing Blocks - Call Contexts

## Trailing Blocks in Different Call Contexts

    Trailing blocks work with various function and method call styles.

### Scenario: with parenthesized calls

### Scenario: Parenthesized Function Calls

        Trailing blocks work after parenthesized argument lists.

        ```simple
        func(arg1, arg2) \x: x * 2
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | works with regular function calls | pass |
| 2 | combines regular args with trailing block | pass |

**Example:** works with regular function calls
    Given val result = apply_twice(3, {NL}: n + 2)
    Then  expect(result).to_equal(7)

**Example:** combines regular args with trailing block
    Given val result = apply_with_base(10, 5) {NL}: n * 2
    Then  expect(result).to_equal(20)

### Scenario: with no-parentheses calls

### Scenario: No-Parentheses Calls

        Trailing blocks work naturally with no-paren call syntax.

        ```simple
        map items \x: x * 2
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | works without parentheses | pass |

**Example:** works without parentheses
    Given val result = double 7 {NL}: n * 2
    Then  expect(result).to_equal(14)

## Feature: Trailing Blocks - Method Chaining

## Method Chaining with Trailing Blocks

    Trailing blocks integrate seamlessly with method chaining patterns,
    enabling fluent functional-style APIs.

### Scenario: with sequential operations

### Scenario: Sequential Method Chains

        Trailing blocks can be chained for sequential transformations.

        ```simple
        items.filter \x: x > 0
             .map \x: x * 2
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | chains filter and map operations | pass |

**Example:** chains filter and map operations
    Given var result = []
    Given var i = 0
    Given var result = []
    Given var i = 0
    Given val nums = [1, -2, 3, -4, 5]
    Given val filtered = filter_list(nums) \x: x > 0
    Given val doubled = map_list(filtered) \x: x * 2
    Then  expect(doubled[0]).to_equal(2)
    Then  expect(doubled[1]).to_equal(6)
    Then  expect(doubled[2]).to_equal(10)

## Feature: Trailing Blocks - DSL Patterns

## DSL-Style Patterns

    Trailing blocks enable domain-specific language patterns similar to Ruby.

### Scenario: with builder patterns

### Scenario: Builder Pattern

        Trailing blocks work well with builder/fluent APIs.

        ```simple
        router.get "/hello" \: "Hello World"
        router.post "/user" \req: process(req)
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | enables DSL-style APIs with trailing blocks | pass |

**Example:** enables DSL-style APIs with trailing blocks
    Given val result = handler()
    Then  expect(result).to_equal(response)

## Feature: Trailing Blocks - Edge Cases

## Edge Case Handling

    Tests for unusual trailing block scenarios.

### Scenario: with nested trailing blocks

### Scenario: Nested Trailing Blocks

        Trailing blocks can be nested when function returns another function.

| # | Example | Status |
|---|---------|--------|
| 1 | handles nested trailing blocks | pass |

**Example:** handles nested trailing blocks
    Given val result = outer \x: x * 2
    Given val final = result(5)
    Then  expect(final).to_equal(10)

### Scenario: with closures

### Scenario: Closure Captures

        Trailing blocks can capture variables from outer scope.

| # | Example | Status |
|---|---------|--------|
| 1 | captures outer variables | pass |

**Example:** captures outer variables
    Given val add10 = make_adder(10)
    Given var captured = 10
    Given val result = add10(5) \x: x + captured
    Then  expect(result).to_equal(15)
    Given var result = []
    Given var i = 0
    Given var result = []
    Given var i = 0


