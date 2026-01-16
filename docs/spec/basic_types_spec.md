# Primitive Types (Basic Types)

*Source: `simple/std_lib/test/features/types/basic_types_spec.spl`*

---

# Primitive Types (Basic Types)

**Feature ID:** #10
**Category:** Types
**Difficulty:** 2/5
**Status:** Complete

## Overview

Simple provides five primitive types that form the foundation of the type system: `i32` (integers),
`f32` (floating-point numbers), `bool` (booleans), `text` (strings), and `Nil` (null/unit type).

These types are **built-in** and available without imports. They support type inference (types can be
omitted when clear from context) and explicit type annotations for clarity and type safety.

## Primitive Types

### i32 - Integers

**Representation:** 64-bit signed integers (despite the name "i32")
**Range:** -9,223,372,036,854,775,808 to 9,223,372,036,854,775,807
**Literals:** `42`, `-100`, `0`

```simple
val x: i32 = 42
val y = -100  # Type inferred as i32
```

**Naming Note:** Currently named `i32` for familiarity with Rust/C, but implemented as 64-bit.
This may be renamed to `i64` in future versions for accuracy.

### f32 - Floating Point

**Representation:** 64-bit IEEE 754 double-precision floats (despite the name "f32")
**Precision:** ~15-17 decimal digits
**Literals:** `3.14`, `-2.5`, `0.0`

```simple
val pi: f32 = 3.14159
val temp = -2.5  # Type inferred as f32
```

**Naming Note:** Named `f32` for consistency with `i32`, but actually 64-bit. May be renamed to `f64`.

### bool - Booleans

**Representation:** True/false values
**Literals:** `true`, `false`
**Operators:** `and`, `or`, `not`

```simple
val active: bool = true
val flag = false  # Type inferred as bool
```

### text - Strings

**Representation:** UTF-8 encoded strings
**Literals:** `'single quotes'`, `"double quotes"`
**Mutability:** Immutable (cannot change characters in-place)

```simple
val name: text = 'Alice'
val message = "Hello, world!"  # Type inferred as text
```

### Nil - Null/Unit Type

**Representation:** Absence of value, similar to `null` or `None`
**Literal:** `nil`
**Use Cases:** Optional values, void functions, error states

```simple
val maybe_value: Option<i32> = nil  # None case
fn side_effect() -> Nil:  # Void function
    print("Done")
```

## Syntax

### Type Annotations

```simple
# Explicit type annotations
val x: i32 = 42
val name: text = 'Alice'
val active: bool = true

# Type inference (annotations optional)
val y = 100        # i32 inferred
val greeting = 'Hi'  # text inferred
val flag = false   # bool inferred
```

### Literals

```simple
# Integer literals
val positive = 42
val negative = -100
val zero = 0

# Float literals (must have decimal point)
val pi = 3.14
val neg_float = -2.5
val zero_float = 0.0

# Boolean literals
val t = true
val f = false

# Text literals (single or double quotes)
val s1 = 'single quotes'
val s2 = "double quotes"

# Nil literal
val n = nil
```

### Arithmetic Operations

```simple
# Integer arithmetic
val sum = 10 + 5      # Addition
val diff = 10 - 3     # Subtraction
val prod = 4 * 5      # Multiplication
val quot = 20 / 4     # Division (integer division)
val rem = 17 % 5      # Modulo (remainder)

# Float arithmetic
val f_sum = 1.5 + 2.5    # 4.0
val f_diff = 5.0 - 1.5   # 3.5
val f_prod = 2.0 * 3.0   # 6.0
val f_quot = 6.0 / 2.0   # 3.0
```

### Comparison Operations

```simple
# Integer comparisons
5 > 3   # Greater than
3 < 5   # Less than
5 >= 5  # Greater than or equal
5 <= 5  # Less than or equal
5 == 5  # Equality
5 != 3  # Inequality

# Float comparisons (same operators)
3.14 > 2.0
1.5 < 2.5
```

### Boolean Operations

```simple
# Logical operators
true and true   # Conjunction
true or false   # Disjunction
not false       # Negation

# Comparison results are booleans
val result = (5 > 3)  # true
val check = (10 == 10) and (5 < 3)  # false
```

## Runtime Representation

Primitive types map to Rust types in `RuntimeValue` enum:

```rust
pub enum RuntimeValue {
    Int(i64),           // i32 in Simple
    Float(f64),         // f32 in Simple
    Bool(bool),         // bool in Simple
    String(String),     // text in Simple
    Nil,                // Nil in Simple
    // ... other variants
}
```

**Performance:**
- Primitives are stack-allocated where possible
- text (String) is heap-allocated
- Comparisons and arithmetic are O(1)

## Key Properties

**Type Inference:**
- Types can be omitted when clear from context
- Literals infer their natural type
- Type annotations override inference

**Type Safety:**
- No implicit conversions between types
- Cannot add i32 + f32 without explicit conversion
- Cannot use i32 where bool is expected

**Immutability:**
- Primitive values are immutable
- `val x = 10; x = 20` is a rebinding, not mutation
- text strings cannot be modified in-place

**Truthiness:**
- Only `bool` type usable in conditionals
- No "falsy" values like 0, empty string, nil
- Must use explicit comparisons: `if x == 0:` not `if x:`

## Comparison with Other Languages

| Feature | Simple | Python | Rust | JavaScript |
|---------|--------|--------|------|------------|
| Integer Type | `i32` (64-bit) | `int` (arbitrary) | `i32`, `i64` | `number` |
| Float Type | `f32` (64-bit) | `float` | `f32`, `f64` | `number` |
| Boolean | `bool` | `bool` | `bool` | `boolean` |
| String | `text` | `str` | `String` | `string` |
| Null/None | `Nil` | `None` | `()` or `Option` | `null`, `undefined` |
| Type Annotations | Optional | Optional (3.5+) | Required | Optional (TS) |
| Type Inference | Yes | Yes | Yes | Yes (TS) |
| Truthiness | No (strict bool) | Yes (many falsy) | No (strict bool) | Yes (many falsy) |
| String Quotes | Single or double | Single or double | Double only | Single or double |

**Key Differences:**
- Simple requires `bool` for conditionals (no truthiness like Python/JS)
- Simple `i32`/`f32` names don't match actual sizes (64-bit)
- Simple has no integer overflow (uses i64 internally)
- Simple has one string type (Rust has `str` vs `String`)

## Common Patterns

### Type Annotations for Clarity

```simple
# Function parameters benefit from type annotations
fn calculate_area(width: i32, height: i32) -> i32:
    return width * height

# Return types make intent clear
fn is_valid(score: i32) -> bool:
    return score >= 0 and score <= 100
```

### Type Inference for Simplicity

```simple
# Local variables can omit types
fn process_score(score: i32):
    val doubled = score * 2  # i32 inferred
    val message = "Score: "  # text inferred
    val valid = score >= 0   # bool inferred
```

### Explicit Conversions

```simple
# No implicit conversions - must be explicit
val i: i32 = 42
val f: f32 = i.to_f32()  # Explicit conversion

# String conversions
val num_str = i.to_string()
```

### Boolean Logic

```simple
# Combine comparisons with boolean operators
fn in_range(x: i32, min: i32, max: i32) -> bool:
    return x >= min and x <= max

# Short-circuit evaluation
if has_permission() and expensive_check():
    # expensive_check() not called if has_permission() is false
```

## Implementation Files

**Core Type System:**
- `src/compiler/src/hir/types.rs` - HIR type representations
- `src/runtime/src/value/core.rs` - RuntimeValue enum and primitive operations

**Parser:**
- `src/parser/src/expressions/mod.rs` - Literal parsing
- `src/parser/src/types_def/mod.rs` - Type annotation parsing

**Type Checker:**
- `src/compiler/src/type_checker.rs` - Type inference and checking

**Tests:**
- `src/driver/tests/interpreter_types_tests.rs` - Rust integration tests
- `simple/std_lib/test/features/types/basic_types_spec.spl` - This file

## Related Features

- **Type Annotations (#2)**: Explicit type syntax
- **Type Inference (#3)**: Automatic type deduction
- **Variables (#1)**: `val`/`var` bindings with types
- **Operators (#16)**: Arithmetic and comparison operators
- **Option/Result (#17)**: Nullable values via Option<T>

## Notes

- **Naming Inconsistency:** `i32` and `f32` are actually 64-bit. This is a known issue.
- **No Unsigned Types:** Only signed integers. Use `i32` for all integers.
- **No Character Type:** Use single-character `text` instead.
- **No Type Coercion:** All conversions must be explicit.
- **String Interning:** text strings may be interned for performance (implementation detail).

## Integer Type (i32)

    Simple's integer type `i32` represents signed integers with 64-bit precision (despite the name).
    Integers support standard arithmetic operations (+, -, *, /, %) and all comparison operators.

    **Runtime Representation:** `RuntimeValue::Int(i64)`

    **Range:** -2^63 to 2^63-1 (64-bit signed)

    **Literals:** Decimal integers without decimal point: `42`, `-100`, `0`

    **Implementation:** `src/runtime/src/value/core.rs:RuntimeValue::Int`

**Given** integer literal syntax without decimal points
        **When** binding to variables
        **Then** creates i32 values with correct values

        **Code Example:**
        ```simple
        val x = 42
        val y = -100
        assert x == 42
        assert y == -100
        ```

        **Runtime Behavior:**
        - Lexer parses decimal digits as IntLiteral token
        - Parser creates IntLiteral AST node
        - Interpreter evaluates to RuntimeValue::Int(i64)
        - Negative sign handled as unary minus operator

        **Type Inference:**
        - Integer literals infer type `i32`
        - No suffix needed (unlike Rust's `42i32`)

        **Implementation:**
        - Lexer: `src/parser/src/lexer.rs:tokenize_number()`
        - Parser: `src/parser/src/expressions/mod.rs:parse_primary()`
        - Interpreter: `src/compiler/src/interpreter.rs:eval_literal()`

        **Common Patterns:**
        ```simple
        val count = 0
        val max_items = 100
        val offset = -5
        ```

**Given** integer arithmetic expressions
            **When** using +, -, *, / operators
            **Then** produces correct integer results

            **Code Example:**
            ```simple
            val a = 10 + 5   # 15
            val b = 10 - 3   # 7
            val c = 4 * 5    # 20
            val d = 20 / 4   # 5 (integer division)
            ```

            **Arithmetic Operations:**
            - `+` Addition
            - `-` Subtraction
            - `*` Multiplication
            - `/` Integer division (truncates toward zero)
            - `%` Modulo (remainder)

            **Integer Division:**
            - `20 / 4` = 5 (exact)
            - `21 / 4` = 5 (truncates decimal)
            - `-21 / 4` = -5 (truncates toward zero)

            **Overflow Behavior:**
            - Uses i64 internally (wide range)
            - No automatic overflow checking
            - Very large results wrap around (implementation detail)

            **Performance:** O(1) for all operations

            **Implementation:**
            - Binary ops: `src/compiler/src/interpreter.rs:eval_binary_op()`
            - Arithmetic: Direct Rust i64 operations

            **Common Patterns:**
            ```simple
            # Average
            val avg = (a + b) / 2

            # Convert to percentage
            val percent = (score * 100) / total
            ```

**Given** modulo operator (%)
            **When** computing remainder of division
            **Then** returns correct remainder

            **Code Example:**
            ```simple
            val r = 17 % 5  # 2 (remainder of 17 / 5)
            assert r == 2
            ```

            **Modulo Semantics:**
            - `a % b` returns remainder of `a / b`
            - Result has same sign as dividend (left operand)
            - `17 % 5` = 2
            - `-17 % 5` = -2
            - `17 % -5` = 2

            **Use Cases:**
            - Check even/odd: `x % 2 == 0`
            - Cycle through range: `index % array.len()`
            - Extract digits: `num % 10`

            **Edge Cases:**
            - `0 % n` = 0
            - `n % 1` = 0
            - `n % 0` = panic (division by zero)

            **Implementation:**
            - Uses Rust `%` operator on i64

            **Common Patterns:**
            ```simple
            # Check if even
            fn is_even(n: i32) -> bool:
                return n % 2 == 0

            # Circular buffer index
            val index = (current + 1) % buffer_size

            # Extract last digit
            val last_digit = number % 10
            ```

## Floating-Point Type (f32)

    Simple's floating-point type `f32` represents real numbers with 64-bit IEEE 754 precision
    (despite the name). Floats support arithmetic and comparison operations.

    **Runtime Representation:** `RuntimeValue::Float(f64)`

    **Precision:** ~15-17 decimal digits

    **Literals:** Numbers with decimal point: `3.14`, `-2.5`, `0.0`

    **Implementation:** `src/runtime/src/value/core.rs:RuntimeValue::Float`

**Given** numeric literals with decimal points
        **When** binding to variables
        **Then** creates f32 values with correct values

        **Code Example:**
        ```simple
        val f1 = 3.14
        val f2 = -2.5
        assert f1 == 3.14
        assert f2 == -2.5
        ```

        **Literal Requirements:**
        - Must include decimal point
        - Can be negative
        - Scientific notation not yet supported

        **Type Inference:**
        - Literals with decimal point infer as f32
        - `3.14` → f32
        - `42` → i32 (no conversion)

        **Precision:**
        - 64-bit IEEE 754 (double precision)
        - ~15-17 significant decimal digits
        - Some decimals not exactly representable (e.g., 0.1)

        **Implementation:**
        - Lexer: `src/parser/src/lexer.rs:tokenize_number()`
        - Parses as f64 in Rust
        - Stored as RuntimeValue::Float(f64)

        **Common Patterns:**
        ```simple
        val pi = 3.14159
        val temperature = -2.5
        val price = 19.99
        ```

**Given** floating-point arithmetic expressions
            **When** using +, -, *, / operators
            **Then** produces correct float results

            **Code Example:**
            ```simple
            val fa = 1.5 + 2.5  # 4.0
            val fb = 5.0 - 1.5  # 3.5
            val fc = 2.0 * 3.0  # 6.0
            ```

            **Arithmetic Operations:**
            - Same operators as integers: +, -, *, /
            - Division always produces float result
            - No modulo operator for floats

            **Floating-Point Division:**
            - `6.0 / 2.0` = 3.0
            - `7.0 / 2.0` = 3.5 (exact, not truncated like integers)
            - `1.0 / 3.0` = 0.333... (limited precision)

            **Precision Considerations:**
            - Results may have rounding errors
            - Avoid exact equality checks with ==
            - Use epsilon comparisons for tolerance

            **Performance:** O(1) hardware floating-point operations

            **Implementation:**
            - Uses Rust f64 arithmetic operators

            **Common Patterns:**
            ```simple
            # Distance formula
            val dist = sqrt((x2 - x1) * (x2 - x1) + (y2 - y1) * (y2 - y1))

            # Average
            val avg = (a + b + c) / 3.0

            # Compound interest
            val amount = principal * (1.0 + rate) ** years
            ```

## Boolean Type (bool)

    Simple's boolean type `bool` represents truth values with two possible values: `true` and `false`.
    Booleans support logical operators (and, or, not) and are required for conditional expressions.

    **Runtime Representation:** `RuntimeValue::Bool(bool)`

    **Values:** `true`, `false`

    **Operators:** `and`, `or`, `not`

    **Implementation:** `src/runtime/src/value/core.rs:RuntimeValue::Bool`

**Given** boolean literal keywords true and false
        **When** binding to variables
        **Then** creates bool values

        **Code Example:**
        ```simple
        val t = true
        val f = false
        assert t == true
        assert f == false
        ```

        **Literals:**
        - `true` - Boolean true value
        - `false` - Boolean false value
        - No truthiness (0, empty string, nil are NOT false)

        **Type Inference:**
        - `true` and `false` literals infer as bool
        - Cannot use i32 or other types as booleans

        **Strict Boolean Context:**
        - Conditionals require bool type
        - `if x:` is error if x is i32
        - Must use `if x == 0:` for integer checks

        **Implementation:**
        - Keywords in lexer: `src/parser/src/lexer.rs`
        - Stored as RuntimeValue::Bool(bool)

        **Common Patterns:**
        ```simple
        val is_valid = true
        val has_error = false
        val is_active = status == "active"
        ```

**Given** boolean logical operators
            **When** combining boolean expressions
            **Then** produces correct logical results

            **Code Example:**
            ```simple
            assert (true and true) == true
            assert (true and false) == false
            assert (true or false) == true
            assert (not false) == true
            ```

            **Logical Operators:**
            - `and` - Logical conjunction (both must be true)
            - `or` - Logical disjunction (at least one must be true)
            - `not` - Logical negation (inverts truth value)

            **Truth Tables:**
            ```
            AND:  T and T = T, T and F = F, F and T = F, F and F = F
            OR:   T or T = T,  T or F = T,  F or T = T,  F or F = F
            NOT:  not T = F,   not F = T
            ```

            **Short-Circuit Evaluation:**
            - `a and b` - if a is false, b not evaluated
            - `a or b` - if a is true, b not evaluated
            - Enables safe checks: `x != nil and x.field > 0`

            **Precedence:**
            - `not` (highest)
            - `and`
            - `or` (lowest)
            - Use parentheses for clarity

            **Implementation:**
            - Short-circuit in interpreter
            - `src/compiler/src/interpreter.rs:eval_logical_op()`

            **Common Patterns:**
            ```simple
            # Range check
            if x >= 0 and x < 100:
                ...

            # Validation with defaults
            if value != nil and value.is_valid():
                ...

            # Multiple conditions
            if (is_admin or is_moderator) and has_permission:
                ...
            ```

## Comparison Operators

    Simple provides six comparison operators that work with i32, f32, and text types,
    returning bool results. All comparisons are type-safe (no mixed-type comparisons).

    **Operators:**
    - `==` (equality)
    - `!=` (inequality)
    - `<` (less than)
    - `>` (greater than)
    - `<=` (less than or equal)
    - `>=` (greater than or equal)

    **Implementation:** `src/compiler/src/interpreter.rs:eval_comparison()`

**Given** integer comparison operators
        **When** comparing i32 values
        **Then** produces correct boolean results

        **Code Example:**
        ```simple
        assert 5 > 3
        assert 3 < 5
        assert 5 >= 5
        assert 5 <= 5
        assert 5 == 5
        assert 5 != 3
        ```

        **All Comparison Operators:**
        - `>` - Greater than
        - `<` - Less than
        - `>=` - Greater than or equal
        - `<=` - Less than or equal
        - `==` - Equal
        - `!=` - Not equal

        **Semantics:**
        - Exact integer comparison
        - No overflow issues (64-bit)
        - Transitive: if a < b and b < c, then a < c

        **Return Type:**
        - All comparisons return `bool`
        - Can be used in conditionals or stored

        **Implementation:**
        - Direct i64 comparison in Rust

        **Common Patterns:**
        ```simple
        # Range validation
        if score >= 0 and score <= 100:
            ...

        # Bounds checking
        if index < list.len():
            val item = list[index]

        # Comparison chains (no chaining syntax yet)
        if min_val <= x and x <= max_val:
            ...
        ```

**Given** floating-point comparison operators
            **When** comparing f32 values
            **Then** produces boolean results based on float semantics

            **Code Example:**
            ```simple
            assert 3.14 > 2.0
            assert 1.5 < 2.5
            ```

            **Float Comparison Semantics:**
            - IEEE 754 comparison rules
            - NaN comparisons always false (if NaN exists)
            - `-0.0 == 0.0` (negative zero equals positive zero)

            **Precision Considerations:**
            - Floating-point rounding errors
            - `0.1 + 0.2 == 0.3` may be false due to representation
            - Use epsilon for approximate equality

            **Best Practices:**
            ```simple
            # Avoid exact equality
            # BAD: if x == 0.3:

            # GOOD: Use tolerance
            fn approx_equal(a: f32, b: f32) -> bool:
                return abs(a - b) < 0.0001

            if approx_equal(x, 0.3):
                ...
            ```

            **Implementation:**
            - Direct f64 comparison in Rust
            - No special NaN handling yet

            **Common Patterns:**
            ```simple
            # Threshold checks
            if temperature > 100.0:
                warn("Too hot!")

            # Range validation
            if price >= 0.0 and price <= max_price:
                ...
            ```
