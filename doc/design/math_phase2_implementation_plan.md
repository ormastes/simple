# Math Language Phase 2-3 Implementation Plan

**Date:** 2026-01-26
**Status:** Planning
**Depends On:** Phase 1 (Complete)
**Related:** `doc/design/math_block_design.md`, `doc/research/math_language_comparison.md`

---

## Overview

This document outlines the implementation plan for Phase 2 and Phase 3 of Simple's math language features.

**Phase 1 (Complete):** `xor`, `@`, dotted operators, `m{}` with `^`
**Phase 2 (This Plan):** Transpose, tensor types, reductions, axis slicing
**Phase 3 (This Plan):** Implicit multiplication, `stat{}` block, DataFrame semantics

---

## Phase 2: Core Math Infrastructure

### 2.1 Transpose Operators

**Priority:** High
**Estimated Complexity:** Medium

#### 2.1.1 Postfix Transpose `'` (m{} only)

**Files to modify:**

| File | Changes |
|------|---------|
| `lexer.spl` | Handle `'` as `TokenKind.Transpose` in math mode |
| `parser.spl` | Add `UnaryOp.Transpose` or postfix operator parsing |
| `hir.spl` | Add `HirUnaryOp.Transpose` |
| `mir.spl` | Add `MirUnaryOp.Transpose` |

**Lexer changes:**

```simple
# In scan_operator_or_delimiter(), handle single quote:
case '\'':
    if self.in_math_block:
        TokenKind.Transpose  # Postfix transpose
    else:
        # Start of char/string literal
        return self.scan_char_or_string()
```

**Parser changes:**

```simple
# Add to UnaryOp enum:
Transpose       # A' (postfix)

# In parse_postfix_expr(), after primary:
me parse_postfix_expr() -> Expr:
    var expr = self.parse_primary_expr()

    loop:
        if self.match_token(TokenKind.Transpose):
            expr = Expr(
                kind: ExprKind.Unary(UnaryOp.Transpose, expr),
                span: expr.span.extend(self.previous().span)
            )
        elif self.match_token(TokenKind.LBracket):
            # ... existing index handling
        else:
            break

    expr
```

**Test cases:**

```simple
describe "Transpose operator '":
    context "inside m{} block":
        it "transposes a matrix":
            val A = [[1, 2], [3, 4]]
            val At = m{ A' }
            expect At == [[1, 3], [2, 4]]

        it "chains with matmul":
            val y = m{ A' @ x }
            expect y.shape == [2]

        it "works in complex expressions":
            val z = m{ (A' A)^-1 A' b }
```

#### 2.1.2 Property Transpose `.T` (outside m{})

**Files to modify:**

| File | Changes |
|------|---------|
| `std_lib/tensor.spl` | Add `.T` and `.t` methods |

**Implementation:**

```simple
# In std_lib/tensor.spl or similar:
impl Tensor<T, 2>:
    fn T() -> Tensor<T, 2>:
        """Transpose (swap last two dimensions)."""
        self.transpose(-2, -1)

    fn t() -> Tensor<T, 2>:
        """Alias for T()."""
        self.T()

impl Tensor<T, N>:
    fn transpose(dim0: i64, dim1: i64) -> Tensor<T, N>:
        """Swap two dimensions."""
        # Implementation via FFI to torch.transpose
        torch.transpose(self, dim0, dim1)
```

**Test cases:**

```simple
describe "Transpose property .T":
    it "transposes outside m{} block":
        val A = [[1, 2], [3, 4]]
        val At = A.T
        expect At == [[1, 3], [2, 4]]

    it "chains with matmul":
        val y = A.T @ x
```

---

### 2.2 Tensor Type System

**Priority:** High
**Estimated Complexity:** High

#### 2.2.1 Type Aliases

**Files to modify:**

| File | Changes |
|------|---------|
| `std_lib/tensor.spl` | Define Tensor, Matrix, Vector types |
| `compiler/types.spl` | Add tensor type support |

**Type definitions:**

```simple
# In std_lib/tensor.spl:

# Base tensor type with element type and rank
struct Tensor<T, const N: i64>:
    data: TensorData<T>
    shape: [i64; N]
    strides: [i64; N]
    device: Device

# Convenient aliases
type Matrix<T> = Tensor<T, 2>
type Vector<T> = Tensor<T, 1>
type Scalar<T> = Tensor<T, 0>

# Common concrete types
type Mat = Matrix<f64>
type Vec = Vector<f64>
type MatF32 = Matrix<f32>
type VecF32 = Vector<f32>
```

#### 2.2.2 Shape Inference

**Compile-time shape checking where possible:**

```simple
# Shape inference rules:
# A: Matrix<f64>  [M, N]
# x: Vector<f64>  [N]
# y = A @ x       [M]  ← inferred

# Broadcasting rules:
# a: [M, 1]
# b: [1, N]
# c = a .+ b      [M, N]  ← broadcast
```

---

### 2.3 Postfix Reduction Methods

**Priority:** High
**Estimated Complexity:** Low

#### 2.3.1 Global Reductions

**Files to modify:**

| File | Changes |
|------|---------|
| `std_lib/tensor.spl` | Add reduction methods |

**Implementation:**

```simple
impl Tensor<T, N>:
    fn sum() -> T:
        """Sum all elements."""
        torch.sum(self)

    fn mean() -> T:
        """Mean of all elements."""
        torch.mean(self)

    fn prod() -> T:
        """Product of all elements."""
        torch.prod(self)

    fn min() -> T:
        """Minimum element."""
        torch.min(self)

    fn max() -> T:
        """Maximum element."""
        torch.max(self)

    fn std() -> T:
        """Standard deviation."""
        torch.std(self)

    fn var() -> T:
        """Variance."""
        torch.var(self)

    fn norm(p: f64 = 2.0) -> T:
        """Lp norm."""
        torch.norm(self, p)
```

#### 2.3.2 Axis Reductions

```simple
impl Tensor<T, N>:
    fn sum(axis: i64, keepdim: bool = false) -> Tensor<T, ?>:
        """Sum along axis."""
        torch.sum(self, dim: axis, keepdim: keepdim)

    fn mean(axis: i64, keepdim: bool = false) -> Tensor<T, ?>:
        """Mean along axis."""
        torch.mean(self, dim: axis, keepdim: keepdim)

    fn min(axis: i64, keepdim: bool = false) -> (Tensor<T, ?>, Tensor<i64, ?>):
        """Min along axis, returns (values, indices)."""
        torch.min(self, dim: axis, keepdim: keepdim)

    fn max(axis: i64, keepdim: bool = false) -> (Tensor<T, ?>, Tensor<i64, ?>):
        """Max along axis, returns (values, indices)."""
        torch.max(self, dim: axis, keepdim: keepdim)

    fn argmin(axis: i64) -> Tensor<i64, ?>:
        """Index of min along axis."""
        torch.argmin(self, dim: axis)

    fn argmax(axis: i64) -> Tensor<i64, ?>:
        """Index of max along axis."""
        torch.argmax(self, dim: axis)
```

**Test cases:**

```simple
describe "Postfix reductions":
    context "global reductions":
        it "computes sum":
            val x = [1.0, 2.0, 3.0, 4.0]
            expect x.sum == 10.0

        it "computes mean":
            val x = [1.0, 2.0, 3.0, 4.0]
            expect x.mean == 2.5

        it "computes std":
            val x = [1.0, 2.0, 3.0, 4.0]
            expect x.std.approx(1.118)

    context "axis reductions":
        it "sums along axis":
            val A = [[1, 2], [3, 4]]
            expect A.sum(axis: 0) == [4, 6]
            expect A.sum(axis: 1) == [3, 7]

        it "finds max with indices":
            val A = [[1, 4], [3, 2]]
            val (vals, idx) = A.max(axis: 1)
            expect vals == [4, 3]
            expect idx == [1, 0]
```

---

### 2.4 Axis-Aware Slicing Syntax

**Priority:** Medium
**Estimated Complexity:** Medium

#### 2.4.1 Enhanced Slicing

**Current:** `arr[1:3]` (1D slicing works)
**Needed:** `arr[1:3, :]`, `arr[:, 0]`, `arr[.., i]`

**Files to modify:**

| File | Changes |
|------|---------|
| `lexer.spl` | Add `TokenKind.DotDotDot` for `...` (ellipsis) |
| `parser.spl` | Enhance index expression parsing |

**Lexer changes:**

```simple
# In scan_operator_or_delimiter():
case '.':
    if self.peek() == '.' and self.peek_next() == '.':
        self.advance()
        self.advance()
        TokenKind.Ellipsis  # ...
    elif self.peek() == '.':
        # existing .. and ..= handling
```

**Parser changes:**

```simple
# Slice expression inside brackets:
# arr[start:end]       → Slice(start, end, None)
# arr[start:end:step]  → Slice(start, end, step)
# arr[:]               → Slice(None, None, None) - all
# arr[..., i]          → Ellipsis followed by index

enum SliceComponent:
    Index(expr: Expr)
    Slice(start: Expr?, end: Expr?, step: Expr?)
    Ellipsis
    NewAxis

me parse_slice_components() -> [SliceComponent]:
    var components: [SliceComponent] = []

    loop:
        if self.match_token(TokenKind.Ellipsis):
            components = components.push(SliceComponent.Ellipsis)
        elif self.match_token(TokenKind.Colon):
            # Parse slice :end or ::step
            val end = if not self.check(TokenKind.Colon) and not self.check(TokenKind.Comma):
                Some(self.parse_expr())
            else:
                None
            val step = if self.match_token(TokenKind.Colon):
                Some(self.parse_expr())
            else:
                None
            components = components.push(SliceComponent.Slice(None, end, step))
        else:
            val expr = self.parse_expr()
            if self.match_token(TokenKind.Colon):
                # start:end or start:end:step
                val end = if not self.check(TokenKind.Colon) and not self.check(TokenKind.Comma):
                    Some(self.parse_expr())
                else:
                    None
                val step = if self.match_token(TokenKind.Colon):
                    Some(self.parse_expr())
                else:
                    None
                components = components.push(SliceComponent.Slice(Some(expr), end, step))
            else:
                components = components.push(SliceComponent.Index(expr))

        if not self.match_token(TokenKind.Comma):
            break

    components
```

**Test cases:**

```simple
describe "Axis-aware slicing":
    it "slices single axis":
        val A = [[1, 2, 3], [4, 5, 6]]
        expect A[0, :] == [1, 2, 3]
        expect A[:, 0] == [1, 4]

    it "slices with ranges":
        val A = [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
        expect A[0:2, 1:3] == [[2, 3], [5, 6]]

    it "uses ellipsis":
        val T = [[[1, 2], [3, 4]], [[5, 6], [7, 8]]]  # 2x2x2
        expect T[..., 0] == [[1, 3], [5, 7]]

    it "uses step":
        val x = [0, 1, 2, 3, 4, 5]
        expect x[::2] == [0, 2, 4]
        expect x[::-1] == [5, 4, 3, 2, 1, 0]
```

---

## Phase 3: Advanced Math Features

### 3.1 Implicit Multiplication (m{} only)

**Priority:** Medium
**Estimated Complexity:** High

#### 3.1.1 Lexer-Based Approach

**Files to modify:**

| File | Changes |
|------|---------|
| `lexer.spl` | Emit `ImplicitMul` token between adjacent tokens |

**Implementation strategy:**

In math mode, after emitting certain tokens, check if the next token should have implicit multiplication:

```simple
# Implicit multiplication rules (m{} only):
# number ident    → 2x means 2*x
# number (        → 2(x+1) means 2*(x+1)
# ) ident         → (x+1)y means (x+1)*y
# ) (             → (a)(b) means (a)*(b)
# ident ident     → xy means x*y (optional, may conflict)
# ident (         → x(y+1) means x*(y+1)

me emit_implicit_mul_if_needed(prev_kind: TokenKind) -> Token?:
    if not self.in_math_block:
        return None

    val next = self.peek_char()

    # After number literal
    if prev_kind == TokenKind.IntLit or prev_kind == TokenKind.FloatLit:
        if is_ident_start(next) or next == '(':
            return Some(Token.new(TokenKind.ImplicitMul, ...))

    # After close paren
    if prev_kind == TokenKind.RParen:
        if is_ident_start(next) or next == '(':
            return Some(Token.new(TokenKind.ImplicitMul, ...))

    # After identifier (careful - may conflict with function calls)
    if prev_kind == TokenKind.Ident:
        if next == '(':
            # Could be function call - need context
            # Skip implicit mul here, handle in parser
            return None

    None
```

**Parser changes:**

```simple
# In multiplicative expression parsing, handle ImplicitMul:
me parse_multiplicative_expr() -> Expr:
    var left = self.parse_power_expr()

    loop:
        if self.match_token(TokenKind.Star) or self.match_token(TokenKind.ImplicitMul):
            val right = self.parse_power_expr()
            left = Expr(kind: ExprKind.Binary(BinOp.Mul, left, right), ...)
        # ... rest of multiplicative handling
```

**Test cases:**

```simple
describe "Implicit multiplication in m{}":
    it "multiplies number and identifier":
        val x = 5
        val result = m{ 2x + 3 }
        expect result == 13

    it "multiplies number and parentheses":
        val x = 2
        val result = m{ 3(x + 1) }
        expect result == 9

    it "multiplies adjacent parentheses":
        val a = 2
        val b = 3
        val result = m{ (a + 1)(b - 1) }
        expect result == 6

    it "handles complex expressions":
        val x = 3
        val result = m{ 2x^2 + 3x + 1 }
        expect result == 28  # 2*9 + 3*3 + 1
```

---

### 3.2 Statistical Formula Block (stat{})

**Priority:** Low
**Estimated Complexity:** High

#### 3.2.1 Grammar Design

```simple
# stat{} block grammar:
stat_block := "stat" "{" stat_body "}"

stat_body := (stat_stmt NEWLINE)*

stat_stmt := model_def
           | fit_stmt
           | predict_stmt
           | summary_stmt

model_def := "model" IDENT "=" formula

formula := term (("+"|"-") term)*

term := factor (("*"|"/"|":") factor)*
      | factor "^" INT
      | func_call

factor := IDENT
        | "1"  # intercept
        | "0"  # no intercept
        | "(" formula ")"

func_call := IDENT "(" formula ")"

fit_stmt := "fit" IDENT "using" fit_method ("on" IDENT)?

fit_method := "linear" | "logistic" | "poisson" | "glm" | IDENT

predict_stmt := "predict" IDENT "from" IDENT

summary_stmt := "summary" IDENT
```

#### 3.2.2 Example Usage

```simple
# Define data
val data = table{
    y: [1.2, 2.3, 3.1, 4.0, 5.2]
    x1: [1, 2, 3, 4, 5]
    x2: [0.1, 0.2, 0.3, 0.4, 0.5]
    group: ["A", "A", "B", "B", "B"]
}

# Statistical modeling
stat{
    # Linear regression
    model m1 = y ~ x1 + x2
    fit m1 using linear on data

    # With interaction
    model m2 = y ~ x1 * x2  # x1 + x2 + x1:x2
    fit m2 using linear on data

    # With transformation
    model m3 = y ~ log(x1) + x2^2
    fit m3 using linear on data

    # Logistic regression
    model m4 = outcome ~ x1 + x2
    fit m4 using logistic on data

    # Get predictions
    predict y_hat from m1

    # Summary statistics
    summary m1
}

# Access results
print m1.coefficients
print m1.r_squared
print m1.p_values
```

#### 3.2.3 Desugaring

```simple
# stat{ model m = y ~ x1 + x2; fit m using linear on data }
# desugars to:

val m = LinearModel(
    formula: Formula.parse("y ~ x1 + x2"),
    data: data
)
m.fit()

# Where Formula.parse creates:
# - Design matrix from x1, x2 columns
# - Response vector from y column
# - Handles categorical variables automatically
```

---

### 3.3 SDN Table → DataFrame Semantics

**Priority:** Medium
**Estimated Complexity:** Medium

#### 3.3.1 Enhanced Table Type

```simple
# In std_lib/table.spl:

struct Table:
    columns: Dict<text, Column>
    row_count: i64

struct Column:
    name: text
    dtype: Type
    data: [Any]

impl Table:
    # Column access
    fn get(name: text) -> Column:
        self.columns[name]

    # Dot syntax for column access
    fn __getattr__(name: text) -> Column:
        self.get(name)

    # Filtering
    fn where(predicate: fn(Row) -> bool) -> Table:
        # Filter rows matching predicate

    fn filter(column: text, op: text, value: Any) -> Table:
        # SQL-like filtering

    # Selection
    fn select(columns: [text]) -> Table:
        # Select specific columns

    # Aggregation
    fn group_by(columns: [text]) -> GroupedTable:
        # Group by columns

    # Joins
    fn join(other: Table, on: text) -> Table:
        # Inner join

    fn left_join(other: Table, on: text) -> Table:
        # Left join
```

#### 3.3.2 Column Methods

```simple
impl Column:
    # Reductions
    fn sum() -> f64
    fn mean() -> f64
    fn std() -> f64
    fn var() -> f64
    fn min() -> Any
    fn max() -> Any
    fn count() -> i64

    # Transformations
    fn map(f: fn(Any) -> Any) -> Column
    fn filter(predicate: fn(Any) -> bool) -> Column

    # Type conversions
    fn as_int() -> Column
    fn as_float() -> Column
    fn as_text() -> Column
```

#### 3.3.3 Example Usage

```simple
val t = table{
    name: ["Alice", "Bob", "Carol", "Dave"]
    age: [25, 30, 35, 28]
    salary: [50000, 60000, 75000, 55000]
    dept: ["Eng", "Sales", "Eng", "Sales"]
}

# Column access and reductions
print t.age.mean          # 29.5
print t.salary.std        # ~10408

# Filtering
val seniors = t.where(age > 28)
print seniors.name        # ["Bob", "Carol"]

# Chained operations
val eng_avg = t
    .where(dept == "Eng")
    .salary
    .mean
print eng_avg             # 62500

# Group by
val by_dept = t.group_by(["dept"])
print by_dept.salary.mean
# dept   | salary_mean
# Eng    | 62500
# Sales  | 57500
```

---

## Implementation Schedule

### Phase 2 Tasks

| Task | Priority | Complexity | Dependencies |
|------|----------|------------|--------------|
| 2.1.1 Transpose `'` | High | Medium | None |
| 2.1.2 Transpose `.T` | High | Low | Tensor type |
| 2.2.1 Tensor type aliases | High | Medium | None |
| 2.2.2 Shape inference | High | High | Tensor types |
| 2.3.1 Global reductions | High | Low | Tensor type |
| 2.3.2 Axis reductions | High | Medium | Global reductions |
| 2.4.1 Enhanced slicing | Medium | Medium | None |

**Suggested order:**
1. Tensor type aliases (2.2.1)
2. Global reductions (2.3.1)
3. Transpose `.T` (2.1.2)
4. Transpose `'` (2.1.1)
5. Axis reductions (2.3.2)
6. Shape inference (2.2.2)
7. Enhanced slicing (2.4.1)

### Phase 3 Tasks

| Task | Priority | Complexity | Dependencies |
|------|----------|------------|--------------|
| 3.1 Implicit multiplication | Medium | High | None |
| 3.2 stat{} block | Low | High | Table type |
| 3.3 DataFrame semantics | Medium | Medium | None |

**Suggested order:**
1. DataFrame semantics (3.3)
2. Implicit multiplication (3.1)
3. stat{} block (3.2)

---

## Test Plan

### Phase 2 Test Files

```
simple/std_lib/test/features/tensor_types_spec.spl
simple/std_lib/test/features/transpose_spec.spl
simple/std_lib/test/features/reductions_spec.spl
simple/std_lib/test/features/axis_slicing_spec.spl
```

### Phase 3 Test Files

```
simple/std_lib/test/features/implicit_mul_spec.spl
simple/std_lib/test/features/stat_block_spec.spl
simple/std_lib/test/features/dataframe_spec.spl
```

---

## Success Criteria

### Phase 2 Complete When:

- [ ] `A'` transposes matrix inside m{}
- [ ] `A.T` transposes matrix outside m{}
- [ ] `Tensor<T, N>`, `Matrix<T>`, `Vector<T>` types work
- [ ] `x.sum`, `x.mean`, `x.std` work
- [ ] `A.sum(axis: 0)` works
- [ ] `A[:, 0]`, `A[1:3, :]` work
- [ ] All tests pass

### Phase 3 Complete When:

- [ ] `m{ 2x + 3 }` parses as `2*x + 3`
- [ ] `stat{ model m = y ~ x; fit m using linear }` works
- [ ] `table.column.mean` works
- [ ] `table.where(cond).column.sum` works
- [ ] All tests pass
