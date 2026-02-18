# Null Coalescing and Try Operator Parser Specification
*Source:* `test/feature/usage/null_coalescing_try_operator_spec.spl`
**Feature IDs:** #PARSER-NULL-001  |  **Category:** Parser / Operators  |  **Status:** In Progress

## Overview



## Overview

Tests for the `??` (null coalescing) and `?` (try) operators in various contexts.
These operators should work correctly in:
- Simple expressions
- Return statements
- For loop bodies
- If expression bodies
- Match arms

## Known Issues

The following patterns cause parse errors:
1. `val x = expr ?? return Err(...)` - "expected expression, found Return"
2. `val x = expr?` inside for loop body - may cause issues
3. `val x = if cond: Some(fn()?) else: None` - "expected identifier, found Val"

## Workarounds

Use explicit if/else or match instead of operators in these contexts.

## Feature: Null Coalescing Operator (??)

### Scenario: simple expressions

| # | Example | Status |
|---|---------|--------|
| 1 | returns left value when present | pass |
| 2 | returns right value when None | pass |
| 3 | chains multiple coalescing | pass |

**Example:** returns left value when present
    Given val opt: i64? = Some(42)
    Given val result = opt ?? 0
    Then  expect(result).to_equal(42)

**Example:** returns right value when None
    Given val opt: i64? = None
    Given val result = opt ?? 99
    Then  expect(result).to_equal(99)

**Example:** chains multiple coalescing
    Given val a: i64? = None
    Given val b: i64? = None
    Given val c: i64? = Some(10)
    Given val result = a ?? b ?? c ?? 0
    Then  expect(result).to_equal(10)

### Scenario: with function calls

| # | Example | Status |
|---|---------|--------|
| 1 | evaluates right side lazily | pass |
| 2 | calls right side when None | pass |

**Example:** evaluates right side lazily
    Given var counter = 0
    Given val opt: i64? = Some(5)
    Given val result = opt ?? increment()
    Then  expect(result).to_equal(5)
    Then  expect(counter).to_equal(0)

**Example:** calls right side when None
    Given var counter = 0
    Given val opt: i64? = None
    Given val result = opt ?? increment()
    Then  expect(result).to_equal(1)
    Then  expect(counter).to_equal(1)

## Feature: Try Operator (?)

### Scenario: with Result type

| # | Example | Status |
|---|---------|--------|
| 1 | unwraps Ok value | pass |
| 2 | propagates Err | pass |

**Example:** unwraps Ok value
    Given val x = get_ok()?
    Given val result = use_ok()

**Example:** propagates Err
    Given val x = get_err()?
    Given val result = use_err()

### Scenario: with Option type

| # | Example | Status |
|---|---------|--------|
| 1 | unwraps Some value | pass |
| 2 | propagates None | pass |

**Example:** unwraps Some value
    Given val x = get_some()?
    Given val result = use_some()

**Example:** propagates None
    Given val x = get_none()?
    Given val result = use_none()

## Feature: Parser Edge Cases

### Scenario: workaround patterns

| # | Example | Status |
|---|---------|--------|
| 1 | explicit if/else instead of ?? return | pass |
| 2 | match instead of ? in for loop | pass |
| 3 | explicit match for optional config | pass |

**Example:** explicit if/else instead of ?? return
    Given val opt = s.parse_int()
    Given val value = opt.unwrap()
    Given val result = parse_value("42")

**Example:** match instead of ? in for loop
    Given var total = 0
    Given val result = item.parse_int()
    Given val result = sum_parsed(["1", "2", "3"])

**Example:** explicit match for optional config
    Given var timeout: i64? = None
    Given val timeout_str = dict["timeout"].unwrap()
    Given val parsed = timeout_str.parse_int()
    Given var config: Dict<text, text> = {}
    Given val result = parse_config(config)

### Scenario: previously reported bugs (now fixed)

BUG: Bootstrap parser error "expected expression, found Return"
            Root cause: bootstrap binary's parse_primary_expr() doesn't handle
            KwReturn in expression position. Source fix exists in both
            src/compiler/parser.spl and src/app/parser/expr/postfix.spl
            but requires bootstrap rebuild to take effect.

| # | Example | Status |
|---|---------|--------|
| 1 | ? in if-expression body | pass |
| 2 | ? in for loop with Result | pass |

**Example:** ? in if-expression body
    Given val parsed = s.parse_int()
    Given val result = if has_value:
    Given val r1 = parse_optional(true, "42")
    Given val r2 = parse_optional(false, "")

**Example:** ? in for loop with Result
    Given val parsed = s.parse_int()
    Given var total = 0
    Given val n = parse_int_result(item)?
    Given val r1 = sum_parsed(["1", "2", "3"])
    Given val r2 = sum_parsed(["1", "abc", "3"])


