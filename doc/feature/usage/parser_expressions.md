# Parser Expression Specification
*Source:* `test/feature/usage/parser_expressions_spec.spl`
**Feature IDs:** #PARSER-EXPR-001 to #PARSER-EXPR-030  |  **Category:** Infrastructure | Parser  |  **Status:** Implemented

## Overview



use std.text.{NL}

Tests that the parser correctly parses various expression forms including
arithmetic, logical, comparison, indexing, method calls, and more.

## Syntax

```simple
# Arithmetic
x + y, x - y, x * y, x / y, x % y, x ** y, x // y

# Comparison
x < y, x > y, x <= y, x >= y, x == y, x != y

# Logical
x and y, x or y, not x

# Method/Field access
obj.method(), obj.field

# Indexing
arr[0], arr[i], arr[1:3]
```

## Feature: Arithmetic Expression Parsing

## Binary Arithmetic Operators

    Tests parsing of addition, subtraction, multiplication, division, etc.

### Scenario: basic operations

| # | Example | Status |
|---|---------|--------|
| 1 | parses addition | pass |
| 2 | parses subtraction | pass |
| 3 | parses multiplication | pass |
| 4 | parses division | pass |
| 5 | parses modulo | pass |
| 6 | parses power | pass |
| 7 | parses integer division | pass |

**Example:** parses addition
    Given val x = 1 + 2
    Then  expect x == 3

**Example:** parses subtraction
    Given val x = 5 - 3
    Then  expect x == 2

**Example:** parses multiplication
    Given val x = 4 * 5
    Then  expect x == 20

**Example:** parses division
    Given val x = 10 / 2
    Then  expect x == 5

**Example:** parses modulo
    Given val x = 7 % 3
    Then  expect x == 1

**Example:** parses power
    Given val x = 2 ** 3
    Then  expect x == 8

**Example:** parses integer division
    Given val x = 7.fdiv(3)
    Then  expect x == 2

### Scenario: operator precedence

| # | Example | Status |
|---|---------|--------|
| 1 | multiplication before addition | pass |
| 2 | parentheses override precedence | pass |
| 3 | nested parentheses | pass |

**Example:** multiplication before addition
    Given val x = 2 + 3 * 4
    Then  expect x == 14

**Example:** parentheses override precedence
    Given val x = (2 + 3) * 4
    Then  expect x == 20

**Example:** nested parentheses
    Given val x = ((1 + 2) * 3)
    Then  expect x == 9

### Scenario: unary operations

| # | Example | Status |
|---|---------|--------|
| 1 | parses unary minus | pass |
| 2 | parses bitwise not | pass |

**Example:** parses unary minus
    Given val x = -5
    Then  expect x == -5

**Example:** parses bitwise not
    Given val x = ~0
    Then  expect x == -1

## Feature: Comparison Expression Parsing

## Comparison Operators

    Tests parsing of comparison operators for equality and ordering.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses less than | pass |
| 2 | parses greater than | pass |
| 3 | parses less than or equal | pass |
| 4 | parses greater than or equal | pass |
| 5 | parses equals | pass |
| 6 | parses not equals | pass |

**Example:** parses less than
    Then  expect (1 < 2) == true

**Example:** parses greater than
    Then  expect (2 > 1) == true

**Example:** parses less than or equal
    Then  expect (2 <= 2) == true

**Example:** parses greater than or equal
    Then  expect (3 >= 2) == true

**Example:** parses equals
    Then  expect (2 == 2) == true

**Example:** parses not equals
    Then  expect (1 != 2) == true

## Feature: Logical Expression Parsing

## Logical Operators

    Tests parsing of boolean logic operators.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses and | pass |
| 2 | parses or | pass |
| 3 | parses not | pass |
| 4 | parses combined logical | pass |

**Example:** parses and
    Given val x = true and false
    Then  expect x == false

**Example:** parses or
    Given val x = true or false
    Then  expect x == true

**Example:** parses not
    Given val x = not true
    Then  expect x == false

**Example:** parses combined logical
    Given val x = (true and false) or true
    Then  expect x == true

## Feature: Method and Field Access Parsing

## Dot Notation for Members

    Tests parsing of method calls and field access on objects.

### Scenario: method calls

| # | Example | Status |
|---|---------|--------|
| 1 | parses no-arg method call | pass |
| 2 | parses method call with args | pass |
| 3 | parses chained method calls | pass |

**Example:** parses no-arg method call
    Given val arr = [1, 2, 3]
    Given val len = arr.len()
    Then  expect len == 3

**Example:** parses method call with args
    Given val arr = [1, 2, 3]
    Then  expect arr.contains(2)

**Example:** parses chained method calls
    Given val arr = [1, 2, 3]
    Given val mapped = arr.map(\x: x * 2)
    Given val result = mapped.filter(\x: x > 2)
    Then  expect result.len() == 2

### Scenario: field access

| # | Example | Status |
|---|---------|--------|
| 1 | parses field access | pass |
| 2 | parses nested field access | pass |

**Example:** parses field access
    Given val p = Point(x: 10, y: 20)
    Then  expect p.x == 10

**Example:** parses nested field access
    Given val o = Outer(inner: Inner(value: 42))
    Then  expect o.inner.value == 42

## Feature: Indexing Expression Parsing

## Square Bracket Indexing

    Tests parsing of array/collection indexing and slicing.

### Scenario: simple indexing

| # | Example | Status |
|---|---------|--------|
| 1 | parses integer index | pass |
| 2 | parses variable index | pass |
| 3 | parses expression index | pass |
| 4 | parses negative index | pass |

**Example:** parses integer index
    Given val arr = [10, 20, 30]
    Then  expect arr[0] == 10

**Example:** parses variable index
    Given val arr = [10, 20, 30]
    Given val i = 1
    Then  expect arr[i] == 20

**Example:** parses expression index
    Given val arr = [10, 20, 30]
    Then  expect arr[1 + 1] == 30

**Example:** parses negative index
    Given val arr = [10, 20, 30]
    Then  expect arr[-1] == 30

### Scenario: slicing

| # | Example | Status |
|---|---------|--------|
| 1 | parses start end slice | pass |
| 2 | parses end slice | pass |
| 3 | parses start slice | pass |

**Example:** parses start end slice
    Given val arr = [0, 1, 2, 3, 4]
    Given val sliced = arr[1:4]
    Then  expect sliced.len() == 3

**Example:** parses end slice
    Given val arr = [0, 1, 2, 3, 4]
    Given val sliced = arr[:3]
    Then  expect sliced.len() == 3

**Example:** parses start slice
    Given val arr = [0, 1, 2, 3, 4]
    Given val sliced = arr[2:]
    Then  expect sliced.len() == 3

## Feature: Function Call Expression Parsing

## Function Invocation Syntax

    Tests parsing of function calls with various argument styles.

### Scenario: positional arguments

| # | Example | Status |
|---|---------|--------|
| 1 | parses no-arg call | pass |
| 2 | parses single arg call | pass |
| 3 | parses multi-arg call | pass |

**Example:** parses no-arg call
    Then  expect get_value() == 42

**Example:** parses single arg call
    Then  expect double(21) == 42

**Example:** parses multi-arg call
    Then  expect add(10, 20, 12) == 42

### Scenario: named arguments

| # | Example | Status |
|---|---------|--------|
| 1 | parses named arguments | pass |

**Example:** parses named arguments
    Given val result = greet(name = "World", greeting = "Hello")
    Then  expect result == "Hello, World!"

## Feature: Path Expression Parsing

## Double Colon Path Syntax

    Tests parsing of module paths and enum variants.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses enum variant | pass |
| 2 | parses nested path | pass |

**Example:** parses enum variant
    Given val c = Color.Red
    Then  expect c == Color.Red

**Example:** parses nested path
    Then  expect get_value() == 42

## Feature: Conditional Expression Parsing

## Inline If Expressions

    Tests parsing of if expressions that return values.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses if-else expression | pass |
| 2 | parses conditional comparison | pass |

**Example:** parses if-else expression
    Given val x = if true: 1 else: 0
    Then  expect x == 1

**Example:** parses conditional comparison
    Given val a = 10
    Given val b = 5
    Given val max = if a > b: a else: b
    Then  expect max == 10

## Feature: Lambda Expression Parsing

## Backslash Lambda Syntax

    Tests parsing of lambda/anonymous function expressions.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses single parameter lambda | pass |
| 2 | parses multi-parameter lambda | pass |
| 3 | parses no-parameter lambda | pass |
| 4 | uses lambda with map | pass |

**Example:** parses single parameter lambda
    Given val f = \x: x + 1
    Then  expect f(41) == 42

**Example:** parses multi-parameter lambda
    Given val f = \a, b: a + b
    Then  expect f(20, 22) == 42

**Example:** parses no-parameter lambda
    Given val f = \: 42
    Then  expect f() == 42

**Example:** uses lambda with map
    Given val arr = [1, 2, 3]
    Given val doubled = arr.map(\x: x * 2)
    Then  expect doubled[0] == 2

## Feature: is/in Expression Parsing

## Type and Membership Tests

    Tests parsing of is (type check) and in (membership) operators.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses is expression | pass |
| 2 | parses in expression | pass |
| 3 | parses not in expression | pass |

**Example:** parses is expression
    Given val opt: Option<i64> = Some(42)
    Then  expect x == 42

**Example:** parses in expression
    Given val list = [1, 2, 3]
    Then  expect 2 in list

**Example:** parses not in expression
    Given val list = [1, 2, 3]
    Then  expect not (5 in list)

## Feature: Nested Expression Parsing

## Complex Nested Expressions

    Tests parsing of deeply nested and complex expressions.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses deeply nested arithmetic | pass |
| 2 | parses nested collections | pass |
| 3 | parses nested method chains | pass |

**Example:** parses deeply nested arithmetic
    Given val x = ((1 + 2) * (3 + 4)) - ((5 - 6) * (7 - 8))
    Then  expect x == 21 - 1

**Example:** parses nested collections
    Given val arr = [[1, 2], [3, 4]]
    Then  expect arr[0][1] == 2

**Example:** parses nested method chains
    Given val arr = [1, 2, 3, 4, 5]
    Given val filtered1 = arr.filter(\x: x > 2)
    Given val mapped = filtered1.map(\x: x * 2)
    Given val result = mapped.filter(\x: x < 10)
    Then  expect result.len() == 2

## Feature: Optional Chaining Expression Parsing

## Safe Navigation with ?.

    Tests parsing of optional chaining and null coalescing.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses optional chaining | pass |
| 2 | parses null coalescing | pass |
| 3 | parses chained optional access | pass |

**Example:** parses optional chaining
    Given val opt: Option<text> = Some("hello")
    Given val len = opt?.len()
    Then  expect len == Some(5)

**Example:** parses null coalescing
    Given val opt: Option<i64> = None
    Given val value = opt ?? 42
    Then  expect value == 42

**Example:** parses chained optional access
    Given val user: Option<User> = Some(User { name: Some("Alice") })
    Given val name = user?.name ?? "Unknown"
    Then  expect name == "Alice"


