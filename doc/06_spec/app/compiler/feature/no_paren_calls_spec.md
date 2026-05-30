# No-Parentheses Function Calls Specification

**Feature ID:** #300-310 | **Category:** Syntax | **Difficulty:** 2/5 | **Status:** Implemented

_Source: `test/feature/usage/no_paren_calls_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 26 |

## Test Structure

### No-Paren Calls - Basic Syntax

#### with single argument

- ✅ calls function with single argument
- ✅ calls with literal argument
- ✅ calls with identifier argument
#### with multiple arguments

- ✅ calls with two arguments
- ✅ calls with three arguments
- ✅ mixes literals and identifiers
### No-Paren Calls - Argument Types

#### with literals

- ✅ passes integer literal
- ✅ passes string literal
- ✅ passes boolean literal
#### with parenthesized expressions

- ✅ passes arithmetic expression
- ✅ passes multiple expressions
### No-Paren Calls - Nested Calls

#### with inner parenthesized calls

- ✅ nests parenthesized call
- ✅ chains multiple functions
### No-Paren Calls - Trailing Lambdas

#### with single argument plus lambda

- ✅ accepts trailing lambda
- ✅ passes multiple args plus lambda
### No-Paren Calls - Method Calls

#### with method calls

- ✅ uses no-paren with helper function
### No-Paren Calls - Context

#### in assignments

- ✅ works in val assignments
- ✅ works in var assignments
#### in return statements

- ✅ works in implicit returns
### No-Paren Calls - String Arguments

#### with string literals

- ✅ passes single string
- ✅ passes string with spaces
### No-Paren Calls - Mixed Syntax

#### with mixed styles

- ✅ mixes paren and no-paren
- ✅ chains multiple mixed calls
### No-Paren Calls - Edge Cases

#### with zero arguments

- ✅ requires parens for zero args
#### with single identifier

- ✅ passes single variable

