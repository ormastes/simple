# Advanced Pattern Matching Specification
*Source:* `test/feature/usage/pattern_matching_advanced_spec.spl`
**Feature IDs:** #PAT-ADV-001 to #PAT-ADV-018  |  **Category:** Language | Pattern Matching  |  **Status:** Implemented

## Overview



use std.text.{NL}

Tests advanced pattern matching features including:
- Match guards (if conditions)
- If let / While let expressions
- Or patterns (|)
- Range patterns (.., ..=)

## Syntax

```simple
# Match guards
match x:
    n if n > 0 => "positive"
    n if n < 0 => "negative"
    _ => "zero"

# If val (if let is deprecated)
if val Some(value) = opt:
    print(value)

# While val (while let is deprecated)
while val Some(item) = iterator.next():
    process(item)

# Or patterns
match x:
    1 | 2 | 3 => "small"
    _ => "large"

# Range patterns
match x:
    0..10 => "single digit"
    10..100 => "double digit"
    _ => "large"
```

## Feature: Match Guards

## Conditional Pattern Matching

    Tests match guards with if conditions.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | matches with basic guard | pass |
| 2 | matches negative with guard | pass |
| 3 | uses binding in guard | pass |
| 4 | falls through when guard fails | pass |

**Example:** matches with basic guard
    Then  expect classify(5) == 1

**Example:** matches negative with guard
    Then  expect classify(-10) == -1

**Example:** uses binding in guard
    Then  expect verify((7, 5)) == 1  # 7 + 5 = 12 > 10

**Example:** falls through when guard fails
    Then  expect test(50) == 10  # 50 > 100? No. 50 > 10? Yes

## Feature: If Val Expressions

## Pattern Matching in If

    Tests if val/var syntax for conditional pattern matching.
    Note: `if let` is deprecated in favor of `if val` (immutable) and `if var` (mutable).

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | matches Some with if val | pass |
| 2 | uses else branch for non-matching | pass |
| 3 | matches Ok with if val | pass |
| 4 | matches Some with if var | pass |

**Example:** matches Some with if val
    Given val opt = Some(42)
    Given var res = 0
    Then  expect res == 42

**Example:** uses else branch for non-matching
    Given val opt: Option<i64> = nil
    Given var res = 0
    Then  expect res == -1

**Example:** matches Ok with if val
    Given val res = Ok(100)
    Given var output = 0
    Then  expect output == 100

**Example:** matches Some with if var
    Given val opt = Some(42)
    Given var res = 0
    Then  expect res == 42

## Feature: While Let Expressions

## Pattern Matching in While

    Tests while let syntax for iterative pattern matching.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | loops while pattern matches | pass |

**Example:** loops while pattern matches
    Given var counter = 3
    Given var sum = 0
    Then  expect sum == 6  # 3 + 2 + 1

## Feature: Or Patterns

## Multiple Patterns with |

    Tests or patterns matching multiple values.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | matches multiple literals | pass |
| 2 | matches medium group | pass |
| 3 | falls through to wildcard | pass |

**Example:** matches multiple literals
    Then  expect classify(2) == 1

**Example:** matches medium group
    Then  expect classify(5) == 2

**Example:** falls through to wildcard
    Then  expect verify(99) == 99

## Feature: Range Patterns

## Range Matching with .. and ..=

    Tests exclusive and inclusive range patterns.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | matches exclusive range | pass |
| 2 | exclusive range excludes end | pass |
| 3 | matches inclusive range | pass |

**Example:** matches exclusive range
    Then  expect classify(5) == 1

**Example:** exclusive range excludes end
    Then  expect classify(10) == 2  # 10 not in 0..10

**Example:** matches inclusive range
    Then  expect classify(5) == 1  # 5 is in 0..=5

## Feature: Numeric Literals

## Hex, Binary, Octal Literals

    Tests various numeric literal formats.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses hex literal | pass |
| 2 | hex arithmetic | pass |
| 3 | parses binary literal | pass |
| 4 | binary with underscores | pass |
| 5 | parses octal literal | pass |

**Example:** parses hex literal
    Given val x = 0xFF
    Then  expect x == 255

**Example:** hex arithmetic
    Given val x = 0x10 + 0x20
    Then  expect x == 48  # 16 + 32

**Example:** parses binary literal
    Given val x = 0b1010
    Then  expect x == 10

**Example:** binary with underscores
    Given val x = 0b1111_0000
    Then  expect x == 240

**Example:** parses octal literal
    Given val x = 0o755
    Then  expect x == 493  # 7*64 + 5*8 + 5


