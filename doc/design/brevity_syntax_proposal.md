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

### Core Operator Traits

```simple
# Arithmetic operators
trait __add__<T, R = Self>:
    fn __add__(other: T) -> R          # a + b

trait __sub__<T, R = Self>:
    fn __sub__(other: T) -> R          # a - b

trait __mul__<T, R = Self>:
    fn __mul__(other: T) -> R          # a * b

trait __div__<T, R = Self>:
    fn __div__(other: T) -> R          # a / b

trait __mod__<T, R = Self>:
    fn __mod__(other: T) -> R          # a % b

trait __pow__<T, R = Self>:
    fn __pow__(exp: T) -> R            # a ^ b

# Right-hand variants (when LHS doesn't implement)
trait __radd__<T, R = Self>:
    fn __radd__(other: T) -> R         # b + a (called on a)

trait __rmul__<T, R = Self>:
    fn __rmul__(other: T) -> R         # b * a (called on a)

# In-place variants
trait __iadd__<T>:
    fn __iadd__(other: T)              # a += b

trait __imul__<T>:
    fn __imul__(other: T)              # a *= b
```

### Unary Operators

```simple
trait __neg__<R = Self>:
    fn __neg__() -> R                  # -a

trait __pos__<R = Self>:
    fn __pos__() -> R                  # +a

trait __not__<R = bool>:
    fn __not__() -> R                  # !a or not a

trait __invert__<R = Self>:
    fn __invert__() -> R               # ~a (bitwise not)
```

### Comparison Operators

```simple
trait __eq__<T>:
    fn __eq__(other: T) -> bool        # a == b

trait __ne__<T>:
    fn __ne__(other: T) -> bool        # a != b

trait __lt__<T>:
    fn __lt__(other: T) -> bool        # a < b

trait __le__<T>:
    fn __le__(other: T) -> bool        # a <= b

trait __gt__<T>:
    fn __gt__(other: T) -> bool        # a > b

trait __ge__<T>:
    fn __ge__(other: T) -> bool        # a >= b
```

### Special Operators

```simple
trait __matmul__<T, R>:
    fn __matmul__(other: T) -> R       # a @ b (matrix multiply)

trait __getitem__<K, V>:
    fn __getitem__(key: K) -> V        # a[k]

trait __setitem__<K, V>:
    fn __setitem__(key: K, value: V)   # a[k] = v

trait __contains__<T>:
    fn __contains__(item: T) -> bool   # item in a

trait __call__<Args, R>:
    fn __call__(args: Args) -> R       # a(args)
```

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
```

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
