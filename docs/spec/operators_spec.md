# Operators (Arithmetic, Comparison, Logical)

*Source: `simple/std_lib/test/features/types/operators_spec.spl`*

---

# Operators (Arithmetic, Comparison, Logical)

**Feature ID:** #30
**Category:** Types
**Difficulty:** 2/5 (Beginner-Intermediate)
**Status:** Complete

## Overview

Operators in Simple provide standard mathematical, comparison, and logical operations following
conventional precedence rules from C-family languages. All operators are infix (between operands)
except unary operators (-, not).

**Operator Categories:**
- **Arithmetic:** +, -, *, /, % (modulo)
- **Comparison:** ==, !=, <, >, <=, >=
- **Logical:** and, or, not
- **Unary:** - (negation), not (logical negation)

## Syntax & Precedence

**Precedence (highest to lowest):**
1. Unary: -, not
2. Multiplicative: *, /, %
3. Additive: +, -
4. Comparison: ==, !=, <, >, <=, >=
5. Logical and
6. Logical or

**Example:**
```simple
2 + 3 * 4      # 14 (not 20) - * has higher precedence
(2 + 3) * 4    # 20 - use parentheses to override
```

## Comparison with Other Languages

| Operator | Simple | Python | JavaScript | Rust | Scala |
|----------|--------|--------|------------|------|-------|
| Add | `+` | `+` | `+` | `+` | `+` |
| Logical AND | `and` | `and` | `&&` | `&&` | `&&` |
| Logical OR | `or` | `or` | `\|\|` | `\|\|` | `\|\|` |
| Logical NOT | `not` | `not` | `!` | `!` | `!` |
| Equality | `==` | `==` | `===` (strict) | `==` | `==` |
| Modulo | `%` | `%` | `%` | `%` | `%` |

## Short-Circuit Evaluation

Logical operators use short-circuit evaluation:
    - `false and expr` → doesn't evaluate expr
- `true or expr` → doesn't evaluate expr

## Implementation Files

**Parser:** `src/parser/src/expressions/mod.rs` - Operator parsing with precedence
**Interpreter:** `src/compiler/src/interpreter.rs` - Operator evaluation
**Tests:** `src/driver/tests/interpreter_expressions_tests.rs`

## Related Features

- **Basic Types (#10):** Operators work on i32, f32, bool
- **Functions (#12):** Operators are expressions, can be used in function bodies
- **Control Flow (#17):** Comparison operators used in if/while conditions

## Arithmetic Operators - Mathematical Operations

    Standard mathematical operators for numeric types (i32, f32).

    **Operators:** +, -, *, /, %
    **Precedence:** * / % (highest), then + -
    **Associativity:** Left-to-right

**Given** two integers
        **When** using + operator
        **Then** returns their sum

**Given** two integers
        **When** using - operator
        **Then** returns their difference

**Given** two integers
        **When** using * operator
        **Then** returns their product

**Given** two integers
        **When** using / operator
        **Then** returns quotient

**Given** two integers
        **When** using % operator
        **Then** returns remainder after division

**Given** expression with mixed operators
        **When** evaluating without parentheses
        **Then** * has higher precedence than +

        **Example:** 2 + 3 * 4 = 2 + 12 = 14 (not 20)

## Comparison Operators - Relational Tests

    Compare values and return boolean results.

    **Operators:** ==, !=, <, >, <=, >=
    **Result:** Always boolean (true/false)
    **Precedence:** Lower than arithmetic, higher than logical

**Given** two equal values
        **When** using == operator
        **Then** returns true

**Given** two different values
        **When** using != operator
        **Then** returns true

**Given** two numbers
        **When** using < or > operators
        **Then** returns true if relation holds

**Given** equal or ordered values
        **When** using <= or >= operators
        **Then** returns true if less/greater or equal

## Logical Operators - Boolean Logic

    Combine boolean expressions using logical operators.

    **Operators:** and, or, not
    **Short-circuit:** and/or evaluate left-to-right, stop when result determined
    **Precedence:** not (highest), then and, then or (lowest)

**Given** two boolean values
        **When** using and operator
        **Then** returns true only if both are true

**Given** two boolean values
        **When** using or operator
        **Then** returns true if at least one is true

**Given** a boolean value
        **When** using not operator
        **Then** returns logical negation

**Given** false and <expression>
        **When** evaluating the and expression
        **Then** <expression> is not evaluated (short-circuit)

        **Pattern:** Avoid expensive computation when unnecessary

## Unary Operators - Single-Operand Operations

    Operators that work on a single operand.

    **Operators:**
    - `-` (unary minus): Numeric negation
    - `not`: Logical negation

    **Precedence:** Highest (applied before binary operators)

**Given** a positive number
        **When** using unary - operator
        **Then** returns negated value
