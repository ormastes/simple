# Brevity Syntax Proposal: Concise Function Calls & Operator Overloading

**Status:** Proposal
**Date:** 2026-01-15
**Related:** `code_shortening_grammar_analysis.md`, `ll1_migration_2026-01-11.md`

## Overview

This proposal adds brevity features and a unified operator interface to Simple, all **LL(1)-compatible**:

### Syntax Features
1. **Space-separated arguments** - `add 1 2 3` instead of `add(1, 2, 3)`
2. **Pipeline operator** - `data |> parse |> filter pred`
3. **Implicit multiplication** - `3x + 2y` instead of `3*x + 2*y`
4. **Power operator `^`** - `x^2` instead of `x.pow(2)` (Julia/MATLAB style)

### Operator Overloading
5. **Dunder interface** - Python-style `__add__`, `__mul__`, `__pow__` methods
6. **Tensor broadcast** - `a + b` auto-broadcasts via operator overloading

---

## Feature 1: Space-Separated Arguments

### Current Syntax
```simple
add(1, 2, 3)
print("hello")
map(list, \x: x * 2)
```

### Proposed Syntax
```simple
add 1 2 3
print "hello"
map list \x: x * 2
```

### LL(1) Analysis

**Key insight:** Function application has **highest precedence** (Haskell model).

**Rule:** Space-separated tokens after identifier = arguments until operator or newline.

```
call_expr = IDENT atom*
atom      = IDENT | NUMBER | STRING | '(' expr ')' | '\' params ':' expr
```

**Parsing decision tree:**
```
IDENT followed by:
  IDENT/NUMBER/STRING/'('/'\'  → function call, consume as arg
  OPERATOR/NEWLINE/','/')'     → end of call
```

**Single token lookahead:** ✅ LL(1) compatible

### Precedence Examples

| Input | Parsed As | Notes |
|-------|-----------|-------|
| `f a b` | `f(a, b)` | Two args |
| `f a + b` | `f(a) + b` | Operator ends call |
| `f (a + b)` | `f(a + b)` | Parens group expression |
| `f a (b + c)` | `f(a, b + c)` | Second arg is grouped |
| `f a b + c d` | `f(a, b) + c(d)` | Two calls with operator |
| `f \x: x * 2` | `f(\x: x * 2)` | Lambda is single arg |

### Method Calls (Keep Dot)

```simple
# Dot required for methods - prevents ambiguity
list.map \x: x * 2
user.set name: "Alice"

# NOT allowed (too ambiguous):
list map \x: x * 2    # Is 'list' a function or receiver?
```

### Grammar

```ebnf
call_expr      = primary_expr arg*
               | primary_expr '.' IDENT arg*    (* method call *)

arg            = atom
               | '(' expr ')'                   (* grouped expression *)
               | lambda_expr                    (* trailing lambda *)
               | IDENT ':' expr                 (* named argument *)

atom           = IDENT | NUMBER | STRING | CHAR | BOOL | NIL

lambda_expr    = '\' [param_list] ':' (expr | block)
```

### Disambiguation Rules

1. **Operators end calls:** `f a + b` → `(f a) + b`
2. **Parens group expressions:** `f (a + b)` → `f(a + b)`
3. **Newlines end calls:** Statement boundary terminates
4. **Commas are optional but allowed:** `f a, b, c` works for transition
5. **Named args use colon:** `f x: 1 y: 2` → `f(x: 1, y: 2)`

---

## Feature 2: Pipeline Operator `|>`

### Syntax
```simple
data |> parse |> filter pred |> save path

# Equivalent to:
save(filter(parse(data), pred), path)
```

### LL(1) Analysis

**Operator:** `|>` (two-character token, unambiguous)

**Precedence:** Lower than all other operators (binds loosest)

```
pipeline_expr = or_expr ('|>' or_expr)*
```

**Single token lookahead:** ✅ LL(1) compatible (prefix `|` only used in bitwise-or which has higher precedence)

### Semantics

```simple
# Desugaring rule:
a |> f        →  f(a)
a |> f b      →  f(a, b)
a |> f b c    →  f(a, b, c)

# Pipeline inserts LHS as FIRST argument
data |> filter pred     →  filter(data, pred)
data |> map \x: x * 2   →  map(data, \x: x * 2)
```

### Examples

```simple
# Data processing
val result = raw_data
    |> parse
    |> validate
    |> filter \x: x.active
    |> map \x: x.name
    |> sort
    |> take 10

# Without pipeline (nested)
val result = take(sort(map(filter(validate(parse(raw_data)),
    \x: x.active), \x: x.name)), 10)
```

### Grammar

```ebnf
pipeline_expr  = logical_or_expr ('|>' logical_or_expr)*
```

---

## Feature 3: Implicit Multiplication

### Syntax
```simple
val y = 3x + 2y - 5z
val area = 2πr
val formula = ax² + bx + c
```

### LL(1) Analysis

**Lexer-level transformation:** No grammar change needed.

**Rule:** `NUMBER` immediately followed by `IDENT` (no whitespace) → insert `*` token.

```
Lexer output:
  "3x"  →  NUMBER(3), STAR, IDENT(x)
  "2πr" →  NUMBER(2), STAR, IDENT(π), STAR, IDENT(r)
```

**Single token lookahead:** ✅ LL(1) compatible (lexer handles it)

### Conflict Avoidance

| Pattern | Interpretation | Rule |
|---------|----------------|------|
| `3x` | `3 * x` | Number + letter = multiply |
| `3_km` | Semantic literal | Underscore = unit suffix |
| `0xFF` | Hex literal | `0x`/`0b`/`0o` = prefix |
| `3e10` | Scientific notation | `e`/`E` + digits = exponent |
| `3.14` | Float literal | Decimal point = float |

**Lexer priority:**
1. Check for `0x`, `0b`, `0o` prefix → hex/binary/octal
2. Check for `e`/`E` followed by digit → scientific notation
3. Check for `_` followed by identifier → semantic literal
4. Otherwise, `NUMBER IDENT` → implicit multiply

### Grammar

No grammar change - handled entirely in lexer.

---

## Feature 4: Power Operator `^`

### Syntax
```simple
val y = x^2          # x squared
val z = 2^10         # 1024
val w = x^0.5        # Square root
val a = 2^3^2        # Right-associative: 2^(3^2) = 512
```

### LL(1) Analysis

**Operator:** `^` (single character, unambiguous)

**Precedence:** Higher than `*` and `/`, lower than unary operators

**Associativity:** Right-associative (like Julia/math convention)

```
power_expr = unary_expr ('^' power_expr)?   # Right-recursive for right-assoc
```

**Single token lookahead:** ✅ LL(1) compatible

### Precedence Table (Updated)

| Precedence | Operators | Associativity |
|------------|-----------|---------------|
| 1 (lowest) | `\|>` | Left |
| 2 | `or` | Left |
| 3 | `and` | Left |
| 4 | `==`, `!=`, `<`, `>`, `<=`, `>=` | Left |
| 5 | `\|`, `&`, `^` (bitwise) | Left |
| 6 | `+`, `-` | Left |
| 7 | `*`, `/`, `%` | Left |
| 8 | `^` (power) | **Right** |
| 9 | Unary `-`, `!`, `not` | Right |
| 10 (highest) | Function application | Left |

### Grammar

```ebnf
power_expr     = unary_expr ('^' power_expr)?
unary_expr     = ('-' | '!' | 'not') unary_expr | postfix_expr
```

---

## Feature 5: Dunder Interface (Operator Overloading)

Simple uses Python-style "dunder" (double underscore) methods for operator overloading.
This provides a **common interface** across all types.

### Complete Operator Reference (Julia-Compatible)

Simple supports all Julia default operators plus Python-style dunder methods.

#### Arithmetic Operators

| Operator | Dunder | Description | Julia |
|----------|--------|-------------|-------|
| `+x` | `__pos__` | Unary plus | ✅ |
| `-x` | `__neg__` | Unary minus | ✅ |
| `x + y` | `__add__` | Addition | ✅ |
| `x - y` | `__sub__` | Subtraction | ✅ |
| `x * y` | `__mul__` | Multiplication | ✅ |
| `x / y` | `__truediv__` | Division | ✅ |
| `x ÷ y` | `__floordiv__` | Integer division | ✅ |
| `x \ y` | `__rdiv__` | Inverse division (y/x) | ✅ |
| `x ^ y` | `__pow__` | Exponentiation | ✅ |
| `x % y` | `__mod__` | Remainder | ✅ |

#### Bitwise Operators

| Operator | Dunder | Description | Julia |
|----------|--------|-------------|-------|
| `~x` | `__invert__` | Bitwise NOT | ✅ |
| `x & y` | `__and__` | Bitwise AND | ✅ |
| `x \| y` | `__or__` | Bitwise OR | ✅ |
| `x ⊻ y` | `__xor__` | Bitwise XOR | ✅ |
| `x ⊼ y` | `__nand__` | Bitwise NAND | ✅ |
| `x ⊽ y` | `__nor__` | Bitwise NOR | ✅ |
| `x << y` | `__lshift__` | Left shift | ✅ |
| `x >> y` | `__rshift__` | Arithmetic right shift | ✅ |
| `x >>> y` | `__urshift__` | Logical right shift | ✅ |

#### Comparison Operators

| Operator | Dunder | Description | Julia |
|----------|--------|-------------|-------|
| `x == y` | `__eq__` | Equality | ✅ |
| `x != y` or `x ≠ y` | `__ne__` | Inequality | ✅ |
| `x < y` | `__lt__` | Less than | ✅ |
| `x <= y` or `x ≤ y` | `__le__` | Less or equal | ✅ |
| `x > y` | `__gt__` | Greater than | ✅ |
| `x >= y` or `x ≥ y` | `__ge__` | Greater or equal | ✅ |

#### Logical Operators (Short-Circuit)

| Operator | Description | Notes |
|----------|-------------|-------|
| `!x` or `not x` | Logical NOT | Not overloadable |
| `x && y` or `x and y` | Short-circuit AND | Not overloadable |
| `x \|\| y` or `x or y` | Short-circuit OR | Not overloadable |

#### Special Operators

| Operator | Dunder | Description |
|----------|--------|-------------|
| `x @ y` | `__matmul__` | Matrix multiplication |
| `x[k]` | `__getitem__` | Index/subscript access |
| `x[k] = v` | `__setitem__` | Index assignment |
| `k in x` | `__contains__` | Membership test |
| `x(...)` | `__call__` | Callable |

#### Numeric Protocol (Torch-Compatible)

| Function | Dunder | Description |
|----------|--------|-------------|
| `abs(x)` | `__abs__` | Absolute value |
| `round(x)` | `__round__` | Round to nearest |
| `floor(x)` | `__floor__` | Round down |
| `ceil(x)` | `__ceil__` | Round up |
| `trunc(x)` | `__trunc__` | Truncate toward zero |
| `int(x)` | `__int__` | Convert to integer |
| `float(x)` | `__float__` | Convert to float |
| `bool(x)` | `__bool__` | Truthiness test |

#### Container Protocol (Torch-Compatible)

| Function | Dunder | Description |
|----------|--------|-------------|
| `len(x)` | `__len__` | Length / size |
| `for e in x` | `__iter__` | Iteration |
| `reversed(x)` | `__reversed__` | Reverse iteration |

#### String Conversion

| Function | Dunder | Description |
|----------|--------|-------------|
| `repr(x)` | `__repr__` | Debug representation |
| `str(x)` | `__str__` | String representation |
| `hash(x)` | `__hash__` | Hash value |

#### Updating Operators (In-Place)

All binary operators have in-place variants with `i` prefix:

| Operator | Dunder | Description |
|----------|--------|-------------|
| `x += y` | `__iadd__` | In-place add |
| `x -= y` | `__isub__` | In-place subtract |
| `x *= y` | `__imul__` | In-place multiply |
| `x /= y` | `__itruediv__` | In-place divide |
| `x ÷= y` | `__ifloordiv__` | In-place integer divide |
| `x ^= y` | `__ipow__` | In-place power |
| `x %= y` | `__imod__` | In-place modulo |
| `x &= y` | `__iand__` | In-place bitwise AND |
| `x \|= y` | `__ior__` | In-place bitwise OR |
| `x ⊻= y` | `__ixor__` | In-place bitwise XOR |
| `x <<= y` | `__ilshift__` | In-place left shift |
| `x >>= y` | `__irshift__` | In-place right shift |

#### Right-Hand Variants

When LHS doesn't implement an operator, RHS's right-hand variant is called:

| Dunder | Called When |
|--------|-------------|
| `__radd__` | `a + b` where `a` has no `__add__` |
| `__rsub__` | `a - b` where `a` has no `__sub__` |
| `__rmul__` | `a * b` where `a` has no `__mul__` |
| `__rtruediv__` | `a / b` where `a` has no `__truediv__` |
| `__rpow__` | `a ^ b` where `a` has no `__pow__` |

### Trait Definitions

```simple
# Arithmetic
trait __add__<T, R = Self>:
    fn __add__(other: T) -> R

trait __sub__<T, R = Self>:
    fn __sub__(other: T) -> R

trait __mul__<T, R = Self>:
    fn __mul__(other: T) -> R

trait __truediv__<T, R = Self>:
    fn __truediv__(other: T) -> R      # /

trait __floordiv__<T, R = Self>:
    fn __floordiv__(other: T) -> R     # ÷

trait __mod__<T, R = Self>:
    fn __mod__(other: T) -> R          # %

trait __pow__<T, R = Self>:
    fn __pow__(exp: T) -> R            # ^

# Bitwise
trait __and__<T, R = Self>:
    fn __and__(other: T) -> R          # &

trait __or__<T, R = Self>:
    fn __or__(other: T) -> R           # |

trait __xor__<T, R = Self>:
    fn __xor__(other: T) -> R          # ⊻

trait __nand__<T, R = Self>:
    fn __nand__(other: T) -> R         # ⊼

trait __nor__<T, R = Self>:
    fn __nor__(other: T) -> R          # ⊽

trait __lshift__<T, R = Self>:
    fn __lshift__(other: T) -> R       # <<

trait __rshift__<T, R = Self>:
    fn __rshift__(other: T) -> R       # >>

trait __urshift__<T, R = Self>:
    fn __urshift__(other: T) -> R      # >>>

# Unary
trait __neg__<R = Self>:
    fn __neg__() -> R                  # -x

trait __pos__<R = Self>:
    fn __pos__() -> R                  # +x

trait __invert__<R = Self>:
    fn __invert__() -> R               # ~x

# Comparison
trait __eq__<T>:
    fn __eq__(other: T) -> bool        # ==

trait __ne__<T>:
    fn __ne__(other: T) -> bool        # !=, ≠

trait __lt__<T>:
    fn __lt__(other: T) -> bool        # <

trait __le__<T>:
    fn __le__(other: T) -> bool        # <=, ≤

trait __gt__<T>:
    fn __gt__(other: T) -> bool        # >

trait __ge__<T>:
    fn __ge__(other: T) -> bool        # >=, ≥

# Special
trait __matmul__<T, R>:
    fn __matmul__(other: T) -> R       # @

trait __getitem__<K, V>:
    fn __getitem__(key: K) -> V        # []

trait __setitem__<K, V>:
    fn __setitem__(key: K, value: V)   # []=

trait __contains__<T>:
    fn __contains__(item: T) -> bool   # in

trait __call__<Args, R>:
    fn __call__(args: Args) -> R       # ()

# Numeric Protocol (Torch-Compatible)
trait __abs__<R = Self>:
    fn __abs__() -> R                  # abs(x)

trait __round__<R = Self>:
    fn __round__() -> R                # round(x)
    fn __round__(ndigits: i32) -> R    # round(x, ndigits)

trait __floor__<R = Self>:
    fn __floor__() -> R                # floor(x)

trait __ceil__<R = Self>:
    fn __ceil__() -> R                 # ceil(x)

trait __trunc__<R = Self>:
    fn __trunc__() -> R                # trunc(x)

trait __int__:
    fn __int__() -> i64                # int(x)

trait __float__:
    fn __float__() -> f64              # float(x)

trait __bool__:
    fn __bool__() -> bool              # bool(x), truthiness

# Container Protocol (Torch-Compatible)
trait __len__:
    fn __len__() -> i64                # len(x)

trait __iter__<T>:
    fn __iter__() -> Iterator<T>       # for e in x

trait __reversed__<T>:
    fn __reversed__() -> Iterator<T>   # reversed(x)

# String Conversion
trait __repr__:
    fn __repr__() -> str               # repr(x)

trait __str__:
    fn __str__() -> str                # str(x)

trait __hash__:
    fn __hash__() -> i64               # hash(x)
```

### Unicode Operator Aliases

Simple supports Unicode aliases for common operators (like Julia):

| ASCII | Unicode | Name |
|-------|---------|------|
| `!=` | `≠` | Not equal |
| `<=` | `≤` | Less or equal |
| `>=` | `≥` | Greater or equal |
| `xor` | `⊻` | XOR |
| `nand` | `⊼` | NAND |
| `nor` | `⊽` | NOR |
| `div` | `÷` | Integer division |
| `sqrt` | `√` | Square root (unary) |
| `cbrt` | `∛` | Cube root (unary) |

### Operator Resolution

When evaluating `a + b`:

1. Check if `a` implements `__add__(typeof(b))`
2. If not, check if `b` implements `__radd__(typeof(a))`
3. If neither, compile error

```simple
# Example: 3 * tensor
# 1. i32 doesn't implement __mul__(Tensor)
# 2. Tensor implements __rmul__(i32) ✓
# 3. Call tensor.__rmul__(3)
```

---

## Feature 6: Tensor Broadcast Operators

### Syntax
```simple
val c = a + b        # Element-wise addition (broadcasts)
val d = a * b        # Element-wise multiplication
val e = a ^ 2        # Element-wise power
val f = a @ b        # Matrix multiplication
```

### Implementation via Dunder Interface

```simple
impl Tensor:
    # Element-wise arithmetic
    fn __add__(other: Tensor) -> Tensor:
        self.broadcast_add(other)

    fn __sub__(other: Tensor) -> Tensor:
        self.broadcast_sub(other)

    fn __mul__(other: Tensor) -> Tensor:
        self.broadcast_mul(other)

    fn __div__(other: Tensor) -> Tensor:
        self.broadcast_div(other)

    fn __pow__(exp: i32) -> Tensor:
        self.element_pow(exp)

    fn __pow__(exp: f64) -> Tensor:
        self.element_pow(exp)

    fn __pow__(exp: Tensor) -> Tensor:
        self.broadcast_pow(exp)

    # Right-hand scalar operations
    fn __radd__(scalar: f64) -> Tensor:
        self.scalar_add(scalar)

    fn __rmul__(scalar: f64) -> Tensor:
        self.scalar_mul(scalar)

    # Matrix operations
    fn __matmul__(other: Tensor) -> Tensor:
        self.matmul(other)

    # Comparison (element-wise, returns bool tensor)
    fn __eq__(other: Tensor) -> Tensor:
        self.element_eq(other)

    fn __lt__(other: Tensor) -> Tensor:
        self.element_lt(other)

    # Numeric protocol (torch-compatible)
    fn __abs__() -> Tensor:
        self.abs()  # Element-wise absolute value

    fn __round__() -> Tensor:
        self.round()  # Element-wise round

    fn __floor__() -> Tensor:
        self.floor()

    fn __ceil__() -> Tensor:
        self.ceil()

    # Container protocol
    fn __len__() -> i64:
        self.shape[0]  # Size of first dimension

    fn __iter__() -> Iterator<Tensor>:
        self.iter()  # Iterate over first dimension

    fn __bool__() -> bool:
        # Note: Like PyTorch, raises error for multi-element tensors
        if self.numel() != 1:
            raise "Boolean value of multi-element tensor is ambiguous"
        self.item() != 0

    # String conversion
    fn __repr__() -> str:
        "Tensor(shape={self.shape}, dtype={self.dtype})"

    fn __str__() -> str:
        self.to_string()
```

### Torch Alignment Notes

The dunder interface is designed for seamless PyTorch-style tensor operations:

1. **Element-wise operations**: `+`, `-`, `*`, `/`, `^` apply element-wise
2. **Broadcasting**: Automatic shape broadcasting via `__radd__`, `__rmul__`, etc.
3. **Matrix multiply**: `@` operator (`__matmul__`) for matrix multiplication
4. **In-place suffix**: PyTorch uses `.abs_()`, we use `__iabs__` dunder pattern
5. **Boolean ambiguity**: `__bool__` raises error for multi-element tensors (PyTorch behavior)
6. **Numeric protocol**: `abs()`, `round()`, `floor()`, `ceil()` work with tensors

### Usage Examples

```simple
# Basic arithmetic
val a = Tensor.randn [3, 4]
val b = Tensor.randn [3, 4]
val c = a + b              # Calls a.__add__(b)
val d = a * b              # Calls a.__mul__(b)
val e = a ^ 2              # Calls a.__pow__(2)

# Scalar operations
val scaled = 3 * a         # Calls a.__rmul__(3)
val shifted = a + 1.0      # Calls a.__add__(1.0)

# Matrix multiplication
val m1 = Tensor.randn [3, 4]
val m2 = Tensor.randn [4, 5]
val m3 = m1 @ m2           # Calls m1.__matmul__(m2), shape [3, 5]

# Math expressions (with implicit multiply)
val x = Tensor.randn [100]
val y = 2x^2 + 3x + 1      # Quadratic formula, element-wise

# Numeric protocol functions
val a = Tensor.from [-1.5, 2.7, -3.2]
val b = abs(a)             # [1.5, 2.7, 3.2] via __abs__
val c = round(a)           # [-2.0, 3.0, -3.0] via __round__
val d = floor(a)           # [-2.0, 2.0, -4.0] via __floor__
val e = ceil(a)            # [-1.0, 3.0, -3.0] via __ceil__

# Container protocol
val t = Tensor.randn [3, 4, 5]
val n = len(t)             # 3 (first dimension) via __len__
for row in t:              # Iterate rows via __iter__
    print(row.shape)       # [4, 5]

# Boolean ambiguity (PyTorch behavior)
val scalar = Tensor.from [1.0]
if scalar:                 # Works: single element via __bool__
    print("truthy")

val multi = Tensor.from [1.0, 2.0]
if multi:                  # Raises: "Boolean value of multi-element tensor is ambiguous"
    ...
```

---

## Summary: LL(1) Compatibility

| Feature | LL(1) Safe | Mechanism |
|---------|------------|-----------|
| Space-separated args | ✅ | Highest precedence for application |
| Pipeline `\|>` | ✅ | Lowest precedence binary operator |
| Implicit multiply | ✅ | Lexer transformation |
| Power `^` | ✅ | Right-associative binary operator |
| Dunder interface | ✅ | No grammar change (method dispatch) |
| Tensor broadcast | ✅ | Uses dunder interface |

**All features are LL(1)-compatible** with single-token lookahead.

---

## Migration

### Phase 1: Add new syntax (backward compatible)
- Both `f(a, b)` and `f a b` work
- Pipeline `|>` added
- Implicit multiply in lexer

### Phase 2: Deprecation warnings (optional)
- Warn on `f(a, b)` style if preferred
- Or keep both forever (Ruby approach)

---

## Implementation Priority

1. **Pipeline `|>`** - Highest value, easiest to implement
2. **Space-separated args** - High value, moderate complexity
3. **Implicit multiply** - Medium value, lexer change only
4. **Tensor broadcast** - Already possible, just needs stdlib impl

---

## References

- [Haskell Function Application](https://www.schoolofhaskell.com/user/anupamjain/function-application)
- [Elixir Pipeline Operator](https://elixir-lang.org/getting-started/enumerables-and-streams.html)
- [Julia Numeric Literals](https://docs.julialang.org/en/v1/manual/integers-and-floating-point-numbers/)
- [Julia Mathematical Operations](https://docs.julialang.org/en/v1/manual/mathematical-operations/)
- [Ruby Method Call Syntax](https://rubyreferences.github.io/rubyref/language/methods-call.html)
- [Python Dunder Methods](https://www.geeksforgeeks.org/python/dunder-magic-methods-python/)
- [Rust std::ops](https://doc.rust-lang.org/std/ops/index.html)
- [Real Python - Operator Overloading](https://realpython.com/operator-function-overloading/)
- [PyTorch Tensor Documentation](https://docs.pytorch.org/docs/stable/tensors.html)
