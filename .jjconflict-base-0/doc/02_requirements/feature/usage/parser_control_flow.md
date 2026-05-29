# Parser Control Flow Specification
*Source:* `test/feature/usage/parser_control_flow_spec.spl`
**Feature IDs:** #PARSER-CF-001 to #PARSER-CF-020  |  **Category:** Infrastructure | Parser  |  **Status:** Implemented

## Overview




Tests that the parser correctly parses control flow statements including
if/elif/else, while, for, match, loop, and suspension operators.

## Syntax

```simple
if condition:
    body
elif condition:
    body
else:
    body

while condition:
    body

for item in collection:
    body

match value:
    case pattern:
        body

loop:
    body
    if done:
        break
```

## Feature: If Statement Parsing

## Conditional Branching

    Tests parsing of if, elif, and else branches.

### Scenario: simple if

| # | Example | Status |
|---|---------|--------|
| 1 | parses if with single statement | pass |
| 2 | parses if with false condition | pass |

**Example:** parses if with single statement
    Given var result = 0
    Then  expect result == 42

**Example:** parses if with false condition
    Given var result = 0
    Then  expect result == 0

### Scenario: if-else

| # | Example | Status |
|---|---------|--------|
| 1 | parses if-else | pass |

**Example:** parses if-else
    Given var result = 0
    Then  expect result == 42

### Scenario: if-elif-else

| # | Example | Status |
|---|---------|--------|
| 1 | parses multiple elif branches | pass |

**Example:** parses multiple elif branches
    Then  expect classify(-5) == "negative"
    Then  expect classify(0) == "zero"
    Then  expect classify(5) == "small"
    Then  expect classify(100) == "large"

### Scenario: nested if

| # | Example | Status |
|---|---------|--------|
| 1 | parses nested if statements | pass |

**Example:** parses nested if statements
    Given var result = 0
    Then  expect result == 42

## Feature: While Loop Parsing

## Conditional Loops

    Tests parsing of while loop statements.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses while loop | pass |
| 2 | parses while with complex condition | pass |
| 3 | parses while false (no iterations) | pass |

**Example:** parses while loop
    Given var x = 0
    Then  expect x == 5

**Example:** parses while with complex condition
    Given var x = 0
    Given var y = 10
    Then  expect x == 5

**Example:** parses while false (no iterations)
    Given var x = 42
    Then  expect x == 42

## Feature: For Loop Parsing

## Collection Iteration

    Tests parsing of for loop statements.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses for-in with array | pass |
| 2 | parses for-in with range | pass |
| 3 | parses for-in with inclusive range | pass |
| 4 | parses for with tuple destructuring | pass |

**Example:** parses for-in with array
    Given var sum = 0
    Then  expect sum == 15

**Example:** parses for-in with range
    Given var sum = 0
    Then  expect sum == 10

**Example:** parses for-in with inclusive range
    Given var sum = 0
    Then  expect sum == 15

**Example:** parses for with tuple destructuring
    Given var sum = 0
    Then  expect sum == 10

## Feature: Match Statement Parsing

## Pattern Matching

    Tests parsing of match statements with various patterns.

### Scenario: literal patterns

| # | Example | Status |
|---|---------|--------|
| 1 | parses match with integer patterns | pass |

**Example:** parses match with integer patterns
    Then  expect describe(0) == "zero"
    Then  expect describe(1) == "one"
    Then  expect describe(99) == "other"

### Scenario: guard clauses

| # | Example | Status |
|---|---------|--------|
| 1 | parses match with guards | pass |

**Example:** parses match with guards
    Then  expect classify(-5) == "negative"
    Then  expect classify(0) == "zero"
    Then  expect classify(5) == "positive"

### Scenario: enum patterns

| # | Example | Status |
|---|---------|--------|
| 1 | parses match with enum variants | pass |

**Example:** parses match with enum variants
    Then  expect handle(Status.Ok(42)) == "ok: 42"

### Scenario: tuple patterns

| # | Example | Status |
|---|---------|--------|
| 1 | parses match with tuple patterns | pass |

**Example:** parses match with tuple patterns
    Then  expect describe_point((0, 0)) == "origin"
    Then  expect describe_point((5, 0)) == "x-axis"

## Feature: Loop Statement Parsing

## Infinite Loops with Break

    Tests parsing of loop statements with break/continue.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses loop with break | pass |
| 2 | parses loop with continue | pass |

**Example:** parses loop with break
    Given var x = 0
    Then  expect x == 5

**Example:** parses loop with continue
    Given var sum = 0
    Given var i = 0
    Then  expect sum == 25  # 1+3+5+7+9

## Feature: Suspension Control Flow Parsing

## Async-by-Default Suspension Operators

    Tests parsing of if~, while~, for~ suspension variants.

### Scenario: suspension if

| # | Example | Status |
|---|---------|--------|
| 1 | parses if~ statement | pass |

**Example:** parses if~ statement
    Given var result = 0
    Then  expect result == 42

### Scenario: suspension while

| # | Example | Status |
|---|---------|--------|
| 1 | parses while~ statement | pass |

**Example:** parses while~ statement
    Given var x = 0
    Then  expect x == 3

### Scenario: suspension for

| # | Example | Status |
|---|---------|--------|
| 1 | parses for~ statement | pass |

**Example:** parses for~ statement
    Given var sum = 0
    Then  expect sum == 6

### Scenario: suspension assignment

| # | Example | Status |
|---|---------|--------|
| 1 | parses ~= assignment | pass |

**Example:** parses ~= assignment
    Given var x = 0
    Then  expect x == 42

## Feature: Return Statement Parsing

## Early Return from Functions

    Tests parsing of return statements.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses return with value | pass |
| 2 | parses early return | pass |
| 3 | parses return without value | pass |

**Example:** parses return with value
    Then  expect get_value() == 42

**Example:** parses early return
    Then  expect check(-5) == "negative"
    Then  expect check(5) == "non-negative"

**Example:** parses return without value
    Then  expect true

## Feature: If Val/Var and While Val Parsing

## Pattern Matching in Conditionals

    Tests parsing of if val, if var, and while val constructs.
    Note: `if let` / `while let` are deprecated; use `if val` / `while val` instead.

### Scenario: if val

| # | Example | Status |
|---|---------|--------|
| 1 | parses if val with Some | pass |
| 2 | parses if val with else | pass |

**Example:** parses if val with Some
    Given val opt = Some(42)
    Given var result = 0
    Then  expect result == 42

**Example:** parses if val with else
    Given val opt: Option<i64> = None
    Given var result = 0
    Then  expect result == -1

### Scenario: if var

| # | Example | Status |
|---|---------|--------|
| 1 | parses if var with Some | pass |

**Example:** parses if var with Some
    Given val opt = Some(10)
    Given var result = 0
    Then  expect result == 10

### Scenario: while val

| # | Example | Status |
|---|---------|--------|
| 1 | parses while val | pass |

**Example:** parses while val
    Given var values = [Some(1), Some(2), Some(3), None]
    Given var sum = 0
    Given var idx = 0
    Then  expect sum == 6

### Scenario: while var

| # | Example | Status |
|---|---------|--------|
| 1 | parses while var | pass |

**Example:** parses while var
    Given var values = [Some(1), Some(2), None]
    Given var sum = 0
    Given var idx = 0
    Then  expect sum == 3

## Feature: Complex Control Flow Parsing

## Nested and Combined Control Flow

    Tests parsing of complex nested control flow structures.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses nested loops | pass |
| 2 | parses mixed control flow | pass |
| 3 | parses deeply nested conditions | pass |

**Example:** parses nested loops
    Given var count = 0
    Then  expect count == 9

**Example:** parses mixed control flow
    Given var result = 0
    Then  expect result == 1 + 3 + 5 + 7

**Example:** parses deeply nested conditions
    Then  expect classify(1, 2, 3) == "all positive"


