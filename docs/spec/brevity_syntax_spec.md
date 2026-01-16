# Brevity Syntax Features

*Source: `simple/std_lib/test/features/syntax/brevity_syntax_spec.spl`*

---

# Brevity Syntax Features

**Feature IDs:** #1080-1086
**Category:** Syntax
**Difficulty:** 3/5
**Status:** Planned

## Overview

Simple provides concise syntax for common patterns, reducing boilerplate while maintaining
LL(1) parseability. These features are inspired by Haskell (space-separated args), Elixir
(pipeline), Julia (implicit multiplication, power operator), and Python (dunder interface).

**Key Features:**
- **Space-separated arguments:** `add 1 2 3` instead of `add(1, 2, 3)`
- **Pipeline operator:** `data |> parse |> filter pred`
- **Implicit multiplication:** `3x + 2y` instead of `3*x + 2*y`
- **Power operator:** `x^2` instead of `x.pow(2)` (Julia/MATLAB style)
- **Dunder interface:** Python-style `__add__`, `__mul__`, `__pow__` for operator overloading
- **Tensor broadcast:** `a + b` auto-broadcasts via dunder interface

## Syntax

### Space-Separated Arguments

```simple
# Function calls without parentheses or commas
print "hello"
add 1 2 3
max 10 20

# Operators end the call (highest precedence for application)
f a + b        # Parsed as: f(a) + b
f (a + b)      # Parsed as: f(a + b)
f a b + c      # Parsed as: f(a, b) + c

# Method calls keep the dot
list.map \x: x * 2
user.set name: "Alice"
```

**Grammar:**
```
call_expr = IDENT atom*
atom = IDENT | NUMBER | STRING | '(' expr ')' | lambda_expr
```

### Pipeline Operator

```simple
# Left-to-right data flow
data |> parse |> filter pred |> save path

# Equivalent to nested calls
save(filter(parse(data), pred), path)

# Multi-line pipelines
result = raw_data
    |> parse
    |> validate
    |> filter \x: x.active
    |> map \x: x.name
    |> take 10
```

**Grammar:**
```
pipeline_expr = logical_or_expr ('|>' logical_or_expr)*
```

### Implicit Multiplication

```simple
# Number followed by identifier = multiplication
val y = 3x + 2y - 5z      # 3*x + 2*y - 5*z
val area = 2πr            # 2*π*r
val quad = ax² + bx + c   # a*x² + b*x + c

# Does NOT apply to:
val hex = 0xFF            # Hex literal (0x prefix)
val sci = 3e10            # Scientific notation
val unit = 100_km         # Semantic literal (underscore)
```

**Lexer rule:** NUMBER immediately followed by IDENT (no space) inserts implicit `*`.

### Tensor Broadcast Operators

```simple
# Operators on tensors auto-broadcast
val a = Tensor.randn [3, 4]
val b = Tensor.randn [3, 4]
val c = a + b             # Element-wise addition
val d = a * b             # Element-wise multiplication
val e = a ** 2            # Element-wise power

# Scalar-tensor operations
val scaled = 3 * tensor   # Broadcast scalar
val shifted = tensor + 1  # Broadcast scalar
```

**No grammar change:** Uses operator overloading on Tensor type.

## Runtime Representation

These features are purely syntactic sugar:

- **Space-separated args:** Desugared to standard function calls
- **Pipeline:** `a |> f b` → `f(a, b)`
- **Implicit multiply:** Lexer inserts `*` token
- **Tensor broadcast:** Operator methods handle broadcasting

## LL(1) Compatibility

All features maintain LL(1) parseability:

| Feature | Mechanism | Lookahead |
|---------|-----------|-----------|
| Space args | Application has highest precedence | 1 token |
| Pipeline | Lowest precedence binary operator | 1 token |
| Implicit * | Lexer transformation | N/A |
| Broadcast | No grammar change | N/A |

Single argument without parentheses.

Multiple space-separated arguments.

Operators end the function call (application binds tightest).

Parentheses group complex expressions as single argument.

Lambda expressions as arguments.

Named arguments with colon syntax.

Basic pipeline with single function.

Pipeline chains left to right.

Pipeline inserts value as first argument.

Pipeline can call methods on result.

Pipelines can span multiple lines.

Number followed by identifier = multiplication.

Multiple implicit multiplications in expression.

Float literal with implicit multiply.

0x prefix is hex, not implicit multiply.

e followed by digit is exponent, not multiply.

Underscore prefix is semantic literal, not multiply.

+ operator broadcasts tensors.

* operator broadcasts tensors.

Scalar operations broadcast to all elements.

NumPy-style broadcasting for compatible shapes.

Basic power operation with integers.

Power operator associates right-to-left like math convention.

Power binds tighter than * and /.

Power with float exponents.

Power with variable operands.

Implicit multiply and power together.

Custom type with __add__ method.

Custom type with __mul__ method.

Right-hand multiplication when LHS doesn't implement.

Custom type with __pow__ method.

Custom equality check.

Unary negation operator.

Matrix multiplication operator.

^ operator for element-wise power on tensors.

Combining space-separated args, pipeline, and implicit multiply.

Math formulas with implicit multiply, power, and tensors.

Custom type with full operator support.

Custom type with __abs__ method for abs() function.

Element-wise absolute value on tensors.

Custom rounding behavior via __round__.

Floor rounding via __floor__.

Ceiling rounding via __ceil__.

Length of tensor (first dimension).

Iteration over tensor rows.

Boolean conversion for single-element tensors.

PyTorch-style ambiguity error for multi-element tensors.

Debug representation via __repr__.

String representation via __str__.

Bitwise AND via __and__.

Bitwise OR via __or__.

Bitwise XOR via __xor__ (Julia-style Unicode).

Bitwise NOT via __invert__.

Left shift via __lshift__.

Arithmetic right shift via __rshift__.

Logical right shift via __urshift__ (Julia-style).

Integer division via __floordiv__ (Julia-style Unicode).
