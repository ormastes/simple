# Advanced Operators Specification
*Source:* `test/feature/usage/operators_advanced_spec.spl`
**Feature IDs:** #OP-ADV-001 to #OP-ADV-030  |  **Category:** Language | Operators  |  **Status:** Implemented

## Overview




Tests advanced operators and language features including:
- Mutability control (let, let mut, var, const, static)
- Lambda expressions
- String operations
- Array and dict methods
- Bitwise operators
- Comparison and logical operators
- Power and floor division
- In operator
- Symbols

## Syntax

```simple
# Mutability
let x = 10       # immutable
let mut y = 10   # mutable with let mut
var z = 10       # mutable with var
const MAX = 100  # constant
static counter = 0  # static variable

# Operators
val a = 12 & 10    # bitwise AND
val b = 2 ** 10    # power
val c = 7.fdiv(2)  # floor division (// is now parallel operator)
val d = "ell" in "hello"  # in operator
```

## Feature: Mutability Control

## let, let mut, var, const, static

    Tests variable mutability declarations.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | let is immutable | pass |
| 2 | var is mutable | pass |
| 3 | var in loop | pass |
| 4 | const declaration | pass |
| 5 | const with arithmetic | pass |
| 6 | const with type annotation | pass |
| 7 | static variable | pass |

**Example:** let is immutable
    Given val x = 10
    Then  expect x == 10

**Example:** var is mutable
    Given var y = 10
    Then  expect y == 30

**Example:** var in loop
    Given var sum = 0
    Given var i = 0
    Then  expect sum == 10  # 0+1+2+3+4

**Example:** const declaration
    Then  expect MAX == 100

**Example:** const with arithmetic
    Then  expect BASE * MULTIPLIER == 50

**Example:** const with type annotation
    Then  expect SIZE == 256

**Example:** static variable
    Then  expect counter == 42

## Feature: Lambda Expressions

## Lambda Syntax

    Tests lambda creation and usage.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | basic lambda | pass |
| 2 | lambda with multiple params | pass |
| 3 | lambda as higher-order | pass |

**Example:** basic lambda
    Given val double = \x: x * 2
    Then  expect double(21) == 42

**Example:** lambda with multiple params
    Given val add = \a, b: a + b
    Then  expect add(10, 32) == 42

**Example:** lambda as higher-order
    Given val inc = {NL}: n + 1
    Then  expect apply(inc, 41) == 42

## Feature: String Operations

## String Methods

    Tests string length, concatenation, interpolation.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | string length | pass |
| 2 | string concatenation | pass |
| 3 | string interpolation | pass |

**Example:** string length
    Given val s = "hello"
    Then  expect s.len() == 5

**Example:** string concatenation
    Given val a = "hello"
    Given val b = "world"
    Given val c = a + " " + b
    Then  expect c.len() == 11

**Example:** string interpolation
    Given val x = 42
    Given val s = "value is {x}"
    Then  expect s.len() == 11

## Feature: Array Methods

## Array Operations

    Tests array length and access.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | array length | pass |

**Example:** array length
    Given val arr = [1, 2, 3, 4, 5]
    Then  expect arr.len() == 5

## Feature: Dict Methods

## Dictionary Operations

    Tests dict length, keys, values, contains_key.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | dict length | pass |
| 2 | dict keys | pass |
| 3 | dict values | pass |
| 4 | dict contains_key | pass |

**Example:** dict length
    Given val d = {"a": 1, "b": 2, "c": 3}
    Then  expect d.len() == 3

**Example:** dict keys
    Given val d = {"x": 10, "y": 20}
    Given val keys = d.keys()
    Then  expect keys.len() == 2

**Example:** dict values
    Given val d = {"a": 5, "b": 10}
    Given val vals = d.values()
    Then  expect vals[0] + vals[1] == 15

**Example:** dict contains_key
    Given val d = {"hello": 1}
    Then  expect d.contains_key("hello")

## Feature: Bitwise Operators

## &, |, ^, <<, >>, ~

    Tests bitwise operations.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | bitwise AND | pass |
| 2 | bitwise OR | pass |
| 3 | bitwise XOR | pass |
| 4 | left shift | pass |
| 5 | right shift | pass |
| 6 | bitwise NOT | pass |

**Example:** bitwise AND
    Then  expect (12 & 10) == 8  # 1100 & 1010 = 1000

**Example:** bitwise OR
    Then  expect (12 | 10) == 14  # 1100 | 1010 = 1110

**Example:** bitwise XOR
    Then  expect (12 xor 10) == 6  # 1100 ^ 1010 = 0110

**Example:** left shift
    Then  expect (1 << 4) == 16

**Example:** right shift
    Then  expect (16 >> 2) == 4

**Example:** bitwise NOT
    Then  expect (~0) == -1

## Feature: Comparison Operators

## <, >, <=, >=, ==, !=

    Tests comparison operations.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | less than | pass |
| 2 | greater than | pass |
| 3 | less than or equal | pass |
| 4 | greater than or equal | pass |
| 5 | equal | pass |
| 6 | not equal | pass |

**Example:** less than
    Then  expect 1 < 2

**Example:** greater than
    Then  expect 2 > 1

**Example:** less than or equal
    Then  expect 2 <= 2

**Example:** greater than or equal
    Then  expect 2 >= 2

**Example:** equal
    Then  expect 2 == 2

**Example:** not equal
    Then  expect 2 != 3

## Feature: Logical Operators

## and, or, not

    Tests logical operations.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | and operator | pass |
| 2 | or operator | pass |
| 3 | not operator | pass |

**Example:** and operator
    Then  expect true and true
    Then  expect not (true and false)

**Example:** or operator
    Then  expect true or false
    Then  expect not (false or false)

**Example:** not operator
    Then  expect not false
    Then  expect not (not true)

## Feature: Power Operator

## ** Exponentiation

    Tests power operator.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | power of zero | pass |
| 2 | power of one | pass |
| 3 | power of three | pass |
| 4 | power of ten | pass |
| 5 | three to fourth | pass |

**Example:** power of zero
    Then  expect (2 ** 0) == 1

**Example:** power of one
    Then  expect (2 ** 1) == 2

**Example:** power of three
    Then  expect (2 ** 3) == 8

**Example:** power of ten
    Then  expect (2 ** 10) == 1024

**Example:** three to fourth
    Then  expect (3 ** 4) == 81

## Feature: Floor Division

## .fdiv() Method

    Tests floor division method (// operator is now for parallel execution).

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | positive floor division | pass |
| 2 | another floor division | pass |
| 3 | negative floor division | pass |
| 4 | exact division | pass |

**Example:** positive floor division
    Then  expect 7.fdiv(2) == 3

**Example:** another floor division
    Then  expect 10.fdiv(3) == 3

**Example:** negative floor division
    Then  expect (-7).fdiv(2) == -4  # rounds toward negative infinity

**Example:** exact division
    Then  expect 8.fdiv(4) == 2

## Feature: In Operator

## x in collection

    Tests membership operator.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | in array present | pass |
| 2 | in array absent | pass |
| 3 | in string present | pass |
| 4 | in string absent | pass |

**Example:** in array present
    Then  expect 2 in [1, 2, 3]

**Example:** in array absent
    Then  expect not (5 in [1, 2, 3])

**Example:** in string present
    Then  expect "ell" in "hello"

**Example:** in string absent
    Then  expect not ("xyz" in "hello")

## Feature: Recursive Functions

## Function Recursion

    Tests recursive function calls.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | factorial | pass |

**Example:** factorial
    Then  expect factorial(3) == 6

## Feature: Nested Data Structures

## Nested Arrays and Structs

    Tests nested data access.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | nested arrays | pass |
| 2 | nested structs | pass |

**Example:** nested arrays
    Given val arr = [[1, 2], [3, 4], [5, 6]]
    Then  expect arr[0][0] + arr[1][1] + arr[2][0] == 10

**Example:** nested structs
    Given val o = Outer(inner: Inner(value: 42))
    Then  expect o.inner.value == 42

## Feature: Early Return

## Multiple Return Paths

    Tests functions with multiple returns.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | early return based on condition | pass |

**Example:** early return based on condition
    Then  expect verify(7) == 2

## Feature: Tuple Destructuring

## Multiple Assignment

    Tests tuple unpacking.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | destructures tuple | pass |

**Example:** destructures tuple
    Given val (a, b, c) = (1, 2, 3)
    Then  expect a + b + c == 6

## Feature: Symbols

## :symbol Syntax

    Tests symbol literals.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | symbol comparison | pass |

**Example:** symbol comparison
    Given val s = :hello
    Then  expect s == :hello


