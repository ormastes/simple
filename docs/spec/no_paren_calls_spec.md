*Source: `simple/test/system/features/no_paren_calls/no_paren_calls_spec.spl`*
*Last Updated: 2026-01-16*

---

# No-Parentheses Function Calls Specification

**Feature IDs:** #300-310
**Category:** Syntax
**Difficulty:** 2/5
**Status:** Implemented

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

- **Callable expressions**: Only identifiers, field access (`obj.method`), and paths (`Module::func`)
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
        expect(true).to(eq(true))

# Multiple arguments
call arg1, arg2, arg3
```

## Basic No-Paren Call Syntax

    Functions can be called without parentheses, with arguments separated by commas.

### Scenario: Single Argument

        Function with one argument can omit parentheses.

        ```simple
        fn double(x):
            x * 2

        val result = double 5  # double(5)
        ```

### Scenario: Multiple Arguments

        Multiple arguments require comma separation.

        ```simple
        fn add(a, b):
            a + b

        val sum = add 10, 20  # add(10, 20)
        ```

## Different Argument Types

    No-paren calls support various argument types: literals, identifiers, expressions.

### Scenario: Literal Arguments

        Integer, float, string, and boolean literals as arguments.

        ```simple
        func 42                 # Integer
        func 3.14               # Float
        func "text"             # String
        func true               # Boolean
        ```

### Scenario: Parenthesized Expressions

        Complex expressions can be wrapped in parentheses.

        ```simple
        func (a + b), (c * d)
        ```

## Nested Function Calls

    Mixing parenthesized and no-paren calls.

### Scenario: Inner Calls with Parens

        Inner calls use parentheses, outer call uses no-paren syntax.

        ```simple
        outer inner(arg)
        ```

## Trailing Lambdas with No-Paren Calls

    Lambda with backslash syntax can be the final argument.

### Scenario: Argument Plus Trailing Lambda

        Combine regular argument with trailing lambda.

        ```simple
        map array \x: x * 2
        ```

## Method Calls with No-Paren Syntax

    Methods accessed via field access can use no-paren syntax.

### Scenario: Method Call Syntax

        Methods can be called without parentheses.

        ```simple
        obj.method arg
        ```

## Statement vs Expression Context

    No-paren calls work at statement level and in assignments.

### Scenario: Assignment Context

        No-paren calls on right side of assignments.

        ```simple
        val result = func arg
        ```

### Scenario: Return Statement Context

        No-paren calls in return expressions.

        ```simple
        fn wrapper(x):
            double x
        ```

## String Literal Arguments

    String literals work naturally with no-paren syntax.

### Scenario: String Literals

        Pass strings without parentheses.

        ```simple
        print "Hello World"
        greet "Alice"
        ```

## Mixing Paren and No-Paren Calls

    Combine both calling styles as needed.

### Scenario: Mixed Call Styles

        Some calls with parens, some without.

        ```simple
        outer inner(x), arg2
        ```

## Edge Case Handling

    Special cases and boundary conditions.

### Scenario: Zero Arguments

        Functions with no arguments require parentheses.

        ```simple
        func()  # Parentheses required for zero args
        ```

### Scenario: Single Identifier Argument

        Passing a single variable.
