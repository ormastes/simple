# Lambda Syntax: `fn():` - Function-Style Lambdas

Simple provides multiple lambda syntaxes for different preferences and use cases. The `fn():` syntax offers a familiar function-like appearance for developers coming from other languages.

## Syntax Overview

```simple
# No parameters
fn(): expression

# Single parameter  
fn(x): expression

# Multiple parameters
fn(x, y, z): expression

# Block body
fn(x):
    statements
    final_expression
```

## Comparison with Other Lambda Syntaxes

Simple supports three lambda syntaxes:

| Syntax | Example | Best For |
|--------|---------|----------|
| `fn():` | `fn(x): x * 2` | Familiar to JS/TS/Python developers |
| `\:` | `\x: x * 2` | Concise, Scala-inspired |
| `\|` | `\|x\| x * 2` | Ruby/Rust-style closures |

All three syntaxes are semantically equivalent and can be used interchangeably.

## Examples

### Basic Usage

```simple
# Map over a list
val numbers = [1, 2, 3, 4, 5]
val doubled = numbers.map(fn(x): x * 2)
# Result: [2, 4, 6, 8, 10]

# Filter
val evens = numbers.filter(fn(x): x % 2 == 0)
# Result: [2, 4]

# No parameters
val supplier = fn(): 42
val value = supplier()  # 42
```

### Block Bodies

```simple
# Multi-line lambda
val transformer = fn(x):
    val step1 = x * 2
    val step2 = step1 + 10
    val step3 = step2 / 3
    step3

val result = transformer(5)  # (5 * 2 + 10) / 3 = 6
```

### BDD/Test Framework Usage

The `fn():` syntax integrates seamlessly with Simple's BDD framework:

```simple
describe "Calculator":
    it "adds numbers correctly":
        val calc = Calculator.new()
        expect(calc.add(2, 3)).to(eq(5))
    
    context "with mocked dependencies", fn():
        before_each(fn():
            setup_mocks()
        )
        
        it "handles edge cases":
            # test code
    )
```

### Higher-Order Functions

```simple
fn apply_twice(f: Any, x: i64) -> i64:
    f(f(x))

val result = apply_twice(fn(n): n + 1, 10)
# Equivalent to: (10 + 1) + 1 = 12
```

### Nested Lambdas

```simple
fn make_adder(x: i64) -> Any:
    return fn(y): x + y

val add_5 = make_adder(5)
val result = add_5(3)  # 8
```

## Type Annotations (Future)

Currently, lambda parameters use type inference. Explicit type annotations will be supported in a future release:

```simple
# Future syntax (not yet implemented)
fn(x: i64): i64: x * 2
fn(name: text, age: i64): text:
    "Hello, {name}! You are {age} years old."
```

## Migration from `\:` Syntax

The `fn():` syntax was added as an alias for `\:` to provide more familiar syntax. Both work identically:

```simple
# These are equivalent
val f1 = fn(x): x * 2
val f2 = \x: x * 2

# Mix and match as preferred
list.map(fn(x): x + 1).filter(\x: x > 5)
```

## Implementation Notes

- `fn():` is parsed as a lambda expression, not a function definition
- The parser distinguishes `fn():` (lambda) from `fn name():` (function definition) by checking if `(` immediately follows `fn`
- Lambda expressions can appear anywhere an expression is expected
- Function definitions are statements and cannot appear in expression position

## Related Documentation

- [Backslash Lambda Syntax](backslash_lambda_syntax.md)
- [Closures and Captures](closures_and_captures.md)
- [BDD Framework Guide](../spec/bdd_framework.md)

## Design Rationale

The `fn():` syntax was introduced to:
1. Reduce the learning curve for developers new to Simple
2. Provide consistency with function definition syntax
3. Support the BDD framework's readability goals
4. Maintain compatibility with the concise `\:` syntax

The choice to support multiple lambda syntaxes reflects Simple's philosophy of being both familiar and expressive.
