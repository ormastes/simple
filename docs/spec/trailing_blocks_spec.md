*Source: `simple/test/system/features/trailing_blocks/trailing_blocks_spec.spl`*
*Last Updated: 2026-01-16*

---

# Trailing Blocks Specification

**Feature IDs:** #450
**Category:** Syntax
**Difficulty:** 3/5
**Status:** Implemented

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

## Basic Trailing Block Syntax

    Trailing blocks use backslash (`\`) to introduce lambda parameters,
    allowing cleaner syntax when passing functions as arguments.

### Scenario: Single Parameter Trailing Block

        A trailing block with one parameter uses `\param: expr` syntax.

        ```simple
        val doubled = map([1, 2, 3]) \x: x * 2
        ```

### Scenario: Multiple Parameters

        Trailing blocks support multiple comma-separated parameters.

        ```simple
        reduce(items, 0) \acc, x: acc + x
        ```

### Scenario: Zero Parameters

        Trailing blocks can have no parameters using `\:` syntax.

        ```simple
        router.get "/health" \: "ok"
        ```

## Inline Expressions vs Block Bodies

    Trailing blocks support both inline expressions (single-line) and
    indented block bodies (multi-statement).

### Scenario: Inline Expressions

        Simple expressions can be written inline after the colon.

        ```simple
        items.map \x: x * 2
        ```

### Scenario: Block Bodies

        Multi-statement blocks use indentation like regular blocks.

        ```simple
        items.each \item:
            print(item)
            process(item)
        ```

## Trailing Blocks in Different Call Contexts

    Trailing blocks work with various function and method call styles.

### Scenario: Parenthesized Function Calls

        Trailing blocks work after parenthesized argument lists.

        ```simple
        func(arg1, arg2) \x: x * 2
        ```

### Scenario: No-Parentheses Calls

        Trailing blocks work naturally with no-paren call syntax.

        ```simple
        map items \x: x * 2
        ```

## Method Chaining with Trailing Blocks

    Trailing blocks integrate seamlessly with method chaining patterns,
    enabling fluent functional-style APIs.

### Scenario: Sequential Method Chains

        Trailing blocks can be chained for sequential transformations.

        ```simple
        items.filter \x: x > 0
             .map \x: x * 2
        ```

## DSL-Style Patterns

    Trailing blocks enable domain-specific language patterns similar to Ruby.

### Scenario: Builder Pattern

        Trailing blocks work well with builder/fluent APIs.

        ```simple
        router.get "/hello" \: "Hello World"
        router.post "/user" \req: process(req)
        ```

## Edge Case Handling

    Tests for unusual trailing block scenarios.

### Scenario: Nested Trailing Blocks

        Trailing blocks can be nested when function returns another function.

### Scenario: Closure Captures

        Trailing blocks can capture variables from outer scope.
