# Trailing Blocks Specification

Trailing blocks (also called "trailing lambdas") provide Ruby-style syntax for passing lambda functions as the last argument to a function or method. They use a backslash (`\`) to introduce parameters, making functional-style code more readable and enabling DSL-like syntax patterns.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #450 |
| Category | Syntax |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/feature/usage/trailing_blocks_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Trailing blocks (also called "trailing lambdas") provide Ruby-style syntax for passing
lambda functions as the last argument to a function or method. They use a backslash (`\`)
to introduce parameters, making functional-style code more readable and enabling DSL-like
syntax patterns.

## Syntax

### Basic Trailing Block

```simple
items.map(\x: x * 2)

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
val doubled = [1, 2, 3].map \x: x * 2
val positives = numbers.filter \x: x > 0

router.get "/hello" \: "Hello World"
router.post "/user" \request: process(request)

items.filter \x: x > 0
.map \x: x * 2
.each \x: print(x)
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/trailing_blocks/result.json` |

## Scenarios

- passes trailing block to function
- works with method-style calls
- accepts multiple parameters
- works with three parameters
- allows zero-parameter blocks
- useful for constant responses
- evaluates inline expression
- supports arithmetic expressions
- can use traditional lambdas for multi-statement logic
- can compute complex expressions inline
- works with regular function calls
- combines regular args with trailing block
- works without parentheses
- chains filter and map operations
- enables DSL-style APIs with trailing blocks
- handles nested trailing blocks
- captures outer variables
