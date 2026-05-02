# Parser Type Annotations Specification
*Source:* `test/feature/usage/parser_type_annotations_spec.spl`
**Feature IDs:** #PARSER-TYPE-001 to #PARSER-TYPE-012  |  **Category:** Infrastructure | Parser  |  **Status:** Implemented

## Overview



Tests that the parser correctly parses type annotations including
SIMD types, unit types, typed strings, and array types.

## Type Syntax

```simple
# SIMD vectors
let v: vec[4, f32] = simd_vec

# Unit types
unit UserId: i64 as uid
unit IpAddr: str | u32 as ip

# Typed strings
let addr = "127.0.0.1"_ip
let path = 'C:/data.txt'_file

# Array types
let arr: [i32] = []       # Dynamic
let fixed: [i32; 10] = [] # Fixed size
```

## Feature: SIMD Type Parsing

## SIMD Vector Types

    Tests parsing of SIMD vector type annotations.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses vec[4, f32] type | pass |
| 2 | parses vec[8, i32] type | pass |
| 3 | parses vec[2, f64] type | pass |
| 4 | parses SIMD function parameters | pass |
| 5 | parses SIMD return type | pass |

**Example:** parses vec[4, f32] type
    Then  expect true

**Example:** parses vec[8, i32] type
    Then  expect true

**Example:** parses vec[2, f64] type
    Then  expect true

**Example:** parses SIMD function parameters
    Then  expect true

**Example:** parses SIMD return type
    Then  expect true

## Feature: Unit Type Declarations

## Unit Type Syntax

    Tests parsing of unit type declarations.

### Scenario: single base unit

| # | Example | Status |
|---|---------|--------|
| 1 | parses unit with single base type | pass |
| 2 | parses unit with suffix | pass |

**Example:** parses unit with single base type
    Given val id: UserId = 42_uid
    Then  expect true

**Example:** parses unit with suffix
    Given val temp: Temperature = 98.6_deg
    Then  expect true

### Scenario: multi-base unit

| # | Example | Status |
|---|---------|--------|
| 1 | parses unit with two base types | pass |
| 2 | parses unit with multiple base types | pass |

**Example:** parses unit with two base types
    Then  expect true

**Example:** parses unit with multiple base types
    Then  expect true

## Feature: Typed String Literals

## String Suffix Syntax

    Tests parsing of strings with unit suffixes.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses string with _ip suffix | pass |
| 2 | parses raw string with _file suffix | pass |
| 3 | parses string with _http suffix | pass |
| 4 | parses string with custom suffix | pass |

**Example:** parses string with _ip suffix
    Then  expect true

**Example:** parses raw string with _file suffix
    Then  expect true

**Example:** parses string with _http suffix
    Then  expect true

**Example:** parses string with custom suffix
    Then  expect true

## Feature: Array Type Syntax

## Array Type Annotations

    Tests parsing of array type annotations.

### Scenario: dynamic arrays

| # | Example | Status |
|---|---------|--------|
| 1 | parses [i32] type | pass |
| 2 | parses [str] type | pass |
| 3 | parses nested array type | pass |

**Example:** parses [i32] type
    Then  expect arr.len() == 3

**Example:** parses [str] type
    Then  expect names.len() == 3

**Example:** parses nested array type
    Then  expect matrix.len() == 2

### Scenario: fixed-size arrays

| # | Example | Status |
|---|---------|--------|
| 1 | parses [i32; 10] type | pass |
| 2 | parses [f64; 3] type | pass |

**Example:** parses [i32; 10] type
    Then  expect arr.len() == 10

**Example:** parses [f64; 3] type
    Then  expect vec.len() == 3

## Feature: Generic Type Annotations

## Generic Type Syntax

    Tests parsing of generic type annotations.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses Option<T> type | pass |
| 2 | parses Result<T, E> type | pass |
| 3 | parses nested generic type | pass |
| 4 | parses generic with multiple params | pass |

**Example:** parses Option<T> type
    Then  expect opt.?

**Example:** parses Result<T, E> type
    Then  expect res.ok.?

**Example:** parses nested generic type
    Then  expect opt.?

**Example:** parses generic with multiple params
    Then  expect map.len() == 1

## Feature: Function Type Annotations

## Function Type Syntax

    Tests parsing of function type annotations.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses fn type annotation | pass |
| 2 | parses fn with multiple params | pass |
| 3 | parses fn returning unit | pass |

**Example:** parses fn type annotation
    Then  expect f(21) == 42

**Example:** parses fn with multiple params
    Then  expect add(20, 22) == 42

**Example:** parses fn returning unit
    Then  expect true

## Feature: Tuple Type Annotations

## Tuple Type Syntax

    Tests parsing of tuple type annotations.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses (i64, str) type | pass |
| 2 | parses triple tuple | pass |
| 3 | parses nested tuple | pass |

**Example:** parses (i64, str) type
    Then  expect pair.0 == 42

**Example:** parses triple tuple
    Then  expect triple.2 == true

**Example:** parses nested tuple
    Then  expect nested.0.0 == 1

## Feature: Reference Type Annotations

## Reference Type Syntax

    Tests parsing of reference type annotations.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses mutable reference | pass |
| 2 | parses immutable reference | pass |

**Example:** parses mutable reference
    Given var n = 41
    Then  expect n == 42

**Example:** parses immutable reference
    Given val n = 21
    Then  expect read_only(n) == 42

## Feature: Complex Type Combinations

## Combined Type Annotations

    Tests parsing of complex combined types.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses Option<[i64]> | pass |
| 2 | parses Result<(i64, str), str> | pass |
| 3 | parses fn returning Option | pass |

**Example:** parses Option<[i64]>
    Then  expect opt.?

**Example:** parses Result<(i64, str), str>
    Then  expect res.ok.?

**Example:** parses fn returning Option
    Then  expect f(42).?


