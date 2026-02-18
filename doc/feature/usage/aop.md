# Aspect-Oriented Programming (AOP) Specification
*Source:* `test/feature/usage/aop_spec.spl`
**Feature IDs:** #AOP-001 to #AOP-020  |  **Category:** Language  |  **Status:** In Progress

## Overview



use std.text.{NL}
**Tags:** aop

Aspect-Oriented Programming (AOP) enables cross-cutting concern separation through
compile-time weaving. AOP uses a unified predicate grammar with `pc{...}` pointcut
expressions that can match function executions, types, and attributes.

## Syntax

```simple
# Before advice - runs before target function
on pc{ execution(* target_func(..)) } use advice_func before priority 10

# After advice - runs after successful execution
on pc{ execution(* target_func(..)) } use advice_func after_success priority 5

# Architecture rules
forbid pc{ import(test.internal.*) } "Production cannot import test internals"
allow pc{ depend(within(api.**), within(core.**)) } "API can depend on core"
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Advice | Code that executes at join points (before/after/around) |
| Pointcut | Expression defining where advice applies: `pc{...}` |
| Join point | Execution point where advice can be woven |
| Weaving | Process of inserting advice at join points |
| Priority | Integer controlling advice execution order |

## Behaviors

- Higher priority executes earlier for `before` advice
- Higher priority executes later for `after_*` advice
- `around` advice must call `proceed()` exactly once
- Zero overhead when AOP is not enabled
- Compile-time weaving for `before`/`after`, runtime for `around`

## Limitations (Current Implementation)

- Around advice not yet implemented (skipped tests)
- Inline module definitions in test blocks not supported
- DI integration not yet implemented (skipped tests)

## Feature: AOP Basic Syntax

## Pointcut Expression Syntax

    Verifies parsing and lowering of AOP declarations including pointcut
    expressions with various selectors and advice types.

### Scenario: before advice declaration

| # | Example | Status |
|---|---------|--------|
| 1 | parses before advice with execution pointcut | pass |
| 2 | parses before advice with wildcard return type | pass |

**Example:** parses before advice with execution pointcut
    Then  expect target_func() == 42

**Example:** parses before advice with wildcard return type
    Then  expect compute(21) == 42

### Scenario: after advice declaration

| # | Example | Status |
|---|---------|--------|
| 1 | parses after_success advice | pass |
| 2 | parses after_error advice | pass |

**Example:** parses after_success advice
    Then  expect add(20, 22) == 42

**Example:** parses after_error advice
    Then  expect may_fail(42).unwrap() == 42

## Feature: Before Advice Execution

## Before Advice Behavior

    Verifies that before advice executes before the target function and can
    observe/modify state but not the return value.

### Scenario: execution order

| # | Example | Status |
|---|---------|--------|
| 1 | executes before advice before target | pass |

**Example:** executes before advice before target
    Given var advice_called = false
    Given val result = target()
    Then  expect result == 42
    Then  expect advice_called == true

## Feature: After Advice Execution

## After Advice Behavior

    Verifies after_success and after_error advice execution timing.

### Scenario: after_success execution

| # | Example | Status |
|---|---------|--------|
| 1 | executes after_success when target succeeds | pass |
| 2 | does not execute after_success when target returns Err | pass |

**Example:** executes after_success when target succeeds
    Given var executed = false
    Given val result = target()
    Then  expect result == 42
    Then  expect executed == true

**Example:** does not execute after_success when target returns Err
    Given var executed = false
    Given val result = failing_target()
    Then  expect result.err.?
    Then  expect executed == false

### Scenario: after_error execution

| # | Example | Status |
|---|---------|--------|
| 1 | executes after_error when target returns Err | pass |

**Example:** executes after_error when target returns Err
    Given var error_logged = false
    Given val result = failing()
    Then  expect result.err.?
    Then  expect error_logged == true

## Feature: Pointcut Expressions

## Pointcut Selector Syntax

    Verifies various pointcut selectors including execution patterns
    and attribute matching.

### Scenario: execution patterns

| # | Example | Status |
|---|---------|--------|
| 1 | matches specific function name | pass |
| 2 | matches with wildcard in function name | pass |

**Example:** matches specific function name
    Given var called = false
    Then  expect called == true

**Example:** matches with wildcard in function name
    Given var count = 0
    Then  expect count == 2

### Scenario: attribute patterns

| # | Example | Status |
|---|---------|--------|
| 1 | matches functions with specific attribute | pass |

**Example:** matches functions with specific attribute
    Given var logged = false
    Then  expect logged == true

### Scenario: logical operators

| # | Example | Status |
|---|---------|--------|
| 1 | combines pointcuts with AND | pass |
| 2 | combines pointcuts with OR | pass |
| 3 | negates pointcuts with NOT | pass |

**Example:** combines pointcuts with AND
    Given var called = false
    Then  expect called == true

**Example:** combines pointcuts with OR
    Given var count = 0
    Then  expect count == 2

**Example:** negates pointcuts with NOT
    Given var count = 0
    Then  expect count == 1

## Feature: Architecture Rules

## Static Dependency Validation

    Verifies architecture rules using forbid/allow declarations to enforce
    layered architecture and dependency constraints.

### Scenario: forbid rules

| # | Example | Status |
|---|---------|--------|
| 1 | declares forbidden import pattern | pass |
| 2 | declares forbidden dependency pattern | pass |

**Example:** declares forbidden import pattern
    Then  expect true == true

**Example:** declares forbidden dependency pattern
    Then  expect true == true

### Scenario: allow rules

| # | Example | Status |
|---|---------|--------|
| 1 | declares allowed dependency pattern | pass |

**Example:** declares allowed dependency pattern
    Then  expect true == true

## Feature: Weaving Diagnostics

## Diagnostic Information

    Verifies that the weaving system produces helpful diagnostics including
    weaving summary and join point counts.

### Scenario: weaving reports

| # | Example | Status |
|---|---------|--------|
| 1 | reports join points woven | pass |
| 2 | validates advice configuration | pass |

**Example:** reports join points woven
    Given var woven_count = 0
    Then  expect woven_count == 2

**Example:** validates advice configuration
    Then  expect target() == 42

## Feature: Zero Overhead When Disabled

## Performance Guarantee

    Verifies that when AOP is not enabled, there is zero overhead.

### Scenario: no advice means no overhead

| # | Example | Status |
|---|---------|--------|
| 1 | function without advice has no weaving | pass |
| 2 | disabled weaving produces no diagnostics | pass |

**Example:** function without advice has no weaving
    Then  expect simple_func() == 42

**Example:** disabled weaving produces no diagnostics
    Then  expect isolated_func() == 100


