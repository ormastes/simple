# Math Block (`m{}`) Design

**Status:** Phase 3 Complete
**Date:** 2026-01-26
**Related:** `doc/research/math_language_comparison.md`, `doc/research/math.md`

## Overview

Implement `m{}` math DSL blocks with special syntax rules that differ from regular Simple code.

## Current State

| Feature | Status | Location |
|---------|--------|----------|
| `^` power operator (m{} only) | **Complete** | `lexer.spl:792-871` |
| `^` error outside m{} | **Complete** | `lexer.spl:792-800` |
| `**` power operator | **Complete** | Works everywhere |
| `xor` keyword | **Complete** | `lexer.spl:61, 952`, `parser.spl:838-850` |
| `@` matmul operator | **Complete** | `parser.spl:982-994` |
| `.+` broadcast add | **Complete** | `lexer.spl:825-826`, `parser.spl:966-969` |
| `.-` broadcast sub | **Complete** | `lexer.spl:828-829`, `parser.spl:972-975` |
| `.*` broadcast mul | **Complete** | `lexer.spl:831-832`, `parser.spl:1020-1022` |
| `./` broadcast div | **Complete** | `lexer.spl:834-835`, `parser.spl:1026-1028` |
| `.^` broadcast pow | **Complete** | `lexer.spl:837-838`, `parser.spl:1047-1051` |
| `m{}` block detection | **Complete** | `lexer.spl:682-688` |
| Math brace depth tracking | **Complete** | `lexer.spl:245-246, 859-870` |
| Transpose `'` (m{} only) | **Complete** | `lexer.spl:309-319`, `parser.spl:1167-1172` |
| Transpose `.T` property | **Complete** | `std_lib/src/tensor.spl` |
| Ellipsis `...` token | **Complete** | `lexer.spl:827-829` |
| Tensor/Matrix/Vector types | **Complete** | `std_lib/src/tensor.spl` |
| Global reductions | **Complete** | `std_lib/src/tensor.spl` |
| Axis reductions | **Complete** | `std_lib/src/tensor.spl` |
| Implicit multiplication | **Complete** | `lexer.spl:304-350`, `parser.spl:1037-1042` |
| `ImplicitMul` token | **Complete** | `lexer.spl:160` |
| Table/DataFrame type | **Complete** | `std_lib/src/table.spl` |

---

## Implemented Features

### Phase 1: Complete

#### 1.1 `xor` Keyword

```simple
val a = 5 xor 3      # Bitwise XOR → 6
val b = 0b1010 xor 0b1100  # → 0b0110
```

**Precedence:** Between `or` and `and`

#### 1.2 `@` MatMul Operator

```simple
val y = A @ x        # Matrix multiplication
val C = A @ B        # Matrix-matrix multiply
```

**Precedence:** Between additive (+, -) and multiplicative (*, /)

#### 1.3 Dotted Operators (Broadcasting)

```simple
val c = a .+ b       # Element-wise add
val d = a .- b       # Element-wise sub
val e = a .* b       # Element-wise mul (Hadamard)
val f = a ./ b       # Element-wise div
val g = a .^ 2       # Element-wise power
```

**Precedence:** Same as their non-dotted counterparts

#### 1.4 `m{}` Math Blocks with `^`

```simple
# Inside m{}: ^ is power operator
m{
    y = x^2 + 2*x + 1
    z = (a + b)^n
}

# Outside m{}: ^ produces error (use ** instead)
val y = x ** 2 + 2 * x + 1
```

**Implementation:**
- Lexer tracks `in_math_block: bool` and `math_brace_depth: i64`
- `m{` pattern detected in `scan_identifier()` enters math mode
- `^` returns `TokenKind.Caret` inside m{}, error outside
- Brace depth tracking ensures proper exit from math mode

---

## Phase 2: Complete

### 2.1 Postfix Transpose `'` (m{} only)

**Status: Complete**

```simple
m{
    y = A' @ x           # A transpose times x
    z = (A' A)^-1 A' b   # Normal equations
}
```

**Implementation:**
- Lexer: `'` returns `TokenKind.Transpose` in math mode (`lexer.spl:309-319`)
- Parser: Postfix unary operator (`parser.spl:1167-1172`)
- HIR/MIR: `HirUnaryOp.Transpose`, `MirUnaryOp.Transpose`

### 2.2 Property Transpose `.T` (outside m{})

**Status: Complete**

```simple
val y = A.T @ x          # Transpose via UFCS property
val z = matrix.T         # Works on any tensor type
```

**Implementation:**
- `std_lib/src/tensor.spl`: `.T()` and `.t()` methods on Tensor type

### 2.3 Tensor Type Aliases

**Status: Complete**

```simple
type Tensor<T, const N: i64>  # Base type
type Matrix<T> = Tensor<T, 2>
type Vector<T> = Tensor<T, 1>
type Scalar<T> = Tensor<T, 0>

# Concrete aliases
type Mat = Matrix<f64>
type Vec = Vector<f64>
```

**Implementation:**
- `std_lib/src/tensor.spl`: Full tensor type system

### 2.4 Global Reductions

**Status: Complete**

```simple
x.sum       # Sum all elements
x.mean      # Mean of all elements
x.std       # Standard deviation
x.var       # Variance
x.min       # Minimum
x.max       # Maximum
x.prod      # Product
x.norm()    # L2 norm
x.norm(1)   # L1 norm
```

### 2.5 Axis Reductions

**Status: Complete**

```simple
A.sum(axis: 0)              # Sum along axis
A.mean(axis: 1, keepdim: true)
val (vals, idx) = A.max(axis: 0)
A.argmin(axis: 1)
A.argmax(axis: 1)
```

### 2.6 Ellipsis Token for Slicing

**Status: Complete**

```simple
A[..., 0]    # All dimensions except last
A[0, ...]    # First element, rest unchanged
```

**Implementation:**
- Lexer: `...` returns `TokenKind.Ellipsis` (`lexer.spl:827-829`)

---

## Phase 3: Complete

### 3.1 Implicit Multiplication (m{} only)

**Status: Complete**

```simple
m{
    y = 2x + 3           # 2*x + 3
    z = Ax + b           # A*x + b
    w = 2pi r^2          # 2*pi*r^2
}
```

**Implementation:**
- Lexer: `ImplicitMul` token (`lexer.spl:158`)
- Lexer: `prev_token_kind` and `pending_token` state tracking (`lexer.spl:250-251`)
- Lexer: `maybe_insert_implicit_mul()` method (`lexer.spl:274-331`)
- Parser: `ImplicitMul` handling in multiplicative parsing (`parser.spl:1031-1037`)

**Supported patterns (m{} only):**
- `number ident` → `2x` becomes `2 * x`
- `number (` → `2(x+1)` becomes `2 * (x+1)`
- `) ident` → `(x+1)y` becomes `(x+1) * y`
- `) (` → `(a)(b)` becomes `(a) * (b)`

### 3.2 Table/DataFrame Type

**Status: Complete**

```simple
use std.table.*

val t = Table.from_dict({
    "name": ["Alice", "Bob"],
    "age": [25, 30]
})

print t.age.mean    # 27.5
```

**Implementation:**
- `std_lib/src/table.spl`: Table and Column types (~600 lines)
- SQL-like operations: `select`, `where`, `filter_by`, `sort_by`
- Aggregation: `group_by`, `agg`, `sum`, `mean`
- Joins: `join`, `left_join`, `right_join`

---

## Operator Precedence (High to Low)

| Level | Operators | Associativity | Scope | Status |
|-------|-----------|---------------|-------|--------|
| 1 | `'` (transpose) | Postfix | m{} only | **Complete** |
| 2 | `**`, `^`, `.^` | Right | `^` m{} only | **Complete** |
| 3 | Implicit mul | Left | m{} only | **Complete** |
| 4 | `*`, `/`, `%`, `.*`, `./` | Left | Everywhere | **Complete** |
| 5 | `@` | Left | Everywhere | **Complete** |
| 6 | `+`, `-`, `.+`, `.-` | Left | Everywhere | **Complete** |
| 7 | Comparison | Left | Everywhere | Existing |
| 8 | `and`, `&&` | Left | Everywhere | Existing |
| 9 | `xor` | Left | Everywhere | **Complete** |
| 10 | `or`, `\|\|` | Left | Everywhere | Existing |

---

## Files Modified

### Phase 1

| File | Changes |
|------|---------|
| `simple/compiler/lexer.spl` | `KwXor`, dotted tokens, math block state, `^` context |
| `simple/compiler/parser.spl` | `parse_xor_expr`, `parse_matmul_expr`, broadcast parsing |
| `simple/compiler/hir.spl` | `MatMul`, `BroadcastAdd/Sub/Mul/Div/Pow` in HirBinOp |
| `simple/compiler/mir.spl` | `Pow`, `MatMul`, broadcast ops in MirBinOp |
| `CLAUDE.md` | Documentation updates |

### Phase 2

| File | Changes |
|------|---------|
| `simple/compiler/lexer.spl` | `Transpose` token, `Ellipsis` token, `'` handling in math mode |
| `simple/compiler/parser.spl` | `UnaryOp.Transpose`, postfix transpose parsing |
| `simple/compiler/hir.spl` | `HirUnaryOp.Transpose` |
| `simple/compiler/mir.spl` | `MirUnaryOp.Transpose` |
| `simple/std_lib/src/tensor.spl` | **NEW** - Full tensor type system with reductions |

### Phase 3

| File | Changes |
|------|---------|
| `simple/compiler/lexer.spl` | `ImplicitMul` token, `maybe_insert_implicit_mul()`, state tracking |
| `simple/compiler/parser.spl` | `ImplicitMul` handling in multiplicative parsing |
| `simple/std_lib/src/table.spl` | **NEW** - DataFrame-like Table type (~600 lines) |

---

## Test Specifications

### Phase 1 Tests
See: `simple/std_lib/test/features/math_language_spec.spl`

Tests cover:
- `xor` keyword operations
- `@` matmul parsing
- Dotted operator parsing
- `m{}` block with `^` power
- Precedence verification
- Error messages for `^` outside m{}

### Phase 2 Tests
See: `simple/std_lib/test/features/tensor_spec.spl`

Tests cover:
- Tensor type aliases (Matrix, Vector, Scalar)
- Transpose `'` operator (m{} only)
- Transpose `.T` property
- Global reductions (sum, mean, std, etc.)
- Axis reductions with keepdim
- Shape manipulation (reshape, squeeze, unsqueeze)
- Tensor construction (zeros, ones, eye, arange)
- Linear algebra (det, inv, solve)
- Elementwise math functions

### Phase 3 Tests
See: `simple/std_lib/test/features/implicit_mul_spec.spl`

Tests cover:
- Number followed by identifier (`2x`)
- Number followed by parentheses (`2(x+1)`)
- Parentheses followed by parentheses (`(a)(b)`)
- Parentheses followed by identifier (`(x+1)y`)
- Complex expressions with implicit mul
- Precedence with power operator
- Edge cases (negative numbers, whitespace)

See: `simple/std_lib/test/features/table_spec.spl`

Tests cover:
- Table construction (from columns, dict)
- Column access (get, dot syntax)
- Column reductions (sum, mean, min, max, std)
- Filtering (where, filter_by)
- Selection (select, drop)
- Sorting (sort_by)
- Grouping and aggregation
- Joins (inner, left, right)
- Computed columns
- Method chaining

---

## Examples

### Phase 1 (Implemented)

```simple
# Bitwise XOR
val a = 5 xor 3              # 6

# Matrix multiplication
val y = A @ x
val C = A @ B @ D

# Broadcasting
val scaled = matrix .* 2.0
val diff = a .- b
val powers = bases .^ exponents

# Math block with power
val quadratic = m{ x^2 + 2*x + 1 }
val distance_sq = m{ x^2 + y^2 + z^2 }

# Equivalent outside m{}
val quadratic = x ** 2 + 2 * x + 1
```

### Phase 2 (Implemented)

```simple
# Transpose in m{} block
m{
    y = A' @ x               # Postfix transpose
    z = (A' A)^-1 A' b       # Normal equations
}

# Transpose outside m{} block
val y = A.T @ x              # Property transpose
val At = matrix.t()          # Method call

# Tensor types
val A: Matrix<f64> = zeros<f64>([3, 4])
val x: Vector<f64> = ones<f64>([4])
val y = A @ x

# Global reductions
print x.sum                   # Sum all elements
print x.mean                  # Mean
print x.std                   # Standard deviation
print x.norm()                # L2 norm

# Axis reductions
print A.sum(axis: 0)          # Sum columns
print A.mean(axis: 1)         # Mean of rows
val (vals, idx) = A.max(axis: 0)  # Max with indices

# Shape manipulation
val B = A.reshape([12])
val C = A.T.squeeze(0)
val D = x.unsqueeze(0)        # Add batch dimension

# Ellipsis slicing
val T = zeros<f64>([2, 3, 4, 5])
print T[..., 0].shape         # [2, 3, 4]
print T[0, ...].shape         # [3, 4, 5]
```

### Phase 3 (Implemented)

```simple
# Implicit multiplication in m{} blocks
m{
    y = 2x + 3               # 2*x + 3 = 13 when x=5
    area = pi r^2            # pi * r^2
    z = 2x^2 + 3x + 1        # Quadratic: 2*x^2 + 3*x + 1

    # Parentheses patterns
    result = 2(x + 1)        # 2 * (x + 1)
    product = (a + 1)(b - 1) # (a + 1) * (b - 1)
}

# Table/DataFrame operations
use std.table.*

val t = Table.from_dict({
    "name": ["Alice", "Bob", "Carol"],
    "age": [25, 30, 35],
    "dept": ["Eng", "Sales", "Eng"]
})

# Column access via dot syntax
print t.age.mean            # 30.0
print t.age.sum             # 90

# Filtering
val seniors = t.where(\row: row["age"] > 28)

# Chained operations
val eng_avg = t
    .where(\row: row["dept"] == "Eng")
    .age
    .mean                   # 30.0

# Grouping and aggregation
val by_dept = t.group_by(["dept"]).agg({
    "age": "mean"
})
```

### Phase 4 (Future)

```simple
# stat{} formula block (proposed)
stat{
    model m = y ~ x1 + x2 + log(x3)
    fit m using linear on data
    predict y_hat from m
}
```

---

## Integration with PyTorch

See: `doc/research/math.md` for PyTorch integration details.

The math operators lower to PyTorch operations:
- `@` → `torch.matmul`
- `.+`, `.-`, `.*`, `./` → element-wise with broadcasting
- `.^` → `torch.pow` with broadcasting
- `^` (m{}) → `torch.pow`
- `**` → `torch.pow`
