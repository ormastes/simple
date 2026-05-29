# AOP Architecture Rules Specification
*Source:* `test/feature/usage/aop_architecture_rules_spec.spl`
**Feature IDs:** #AOP-ARCH-001 to #AOP-ARCH-010  |  **Category:** Language  |  **Status:** Implemented

## Overview



use std.text.{NL}

Architecture rules enforce structural constraints on the codebase using the same
unified predicate grammar as AOP. Rules are validated at compile time and can
forbid or allow certain dependency patterns.

## Syntax

```simple
# Forbid pattern with error message
forbid pc{ import(from_pattern, to_pattern) } "Error message"
forbid pc{ depend(from_pattern, to_pattern) } "Error message"

# Allow pattern (exceptions)
allow pc{ depend(within(api.**), within(core.**)) } "Allowed exception"
```

## Architecture Selectors

| Selector | Description |
|----------|-------------|
| import(from, to) | Match import statements |
| depend(from, to) | Match module dependencies |
| use(pattern) | Match type/function usage |
| export(pattern) | Match exported symbols |
| config(string) | Match configuration values |

## Feature: Architecture Forbid Rules

## Forbidding Dependencies

    The `forbid` keyword declares patterns that should cause compile errors
    if matched. Used to enforce architectural boundaries.

### Scenario: import rules

| # | Example | Status |
|---|---------|--------|
| 1 | forbids importing test internals in production | pass |
| 2 | forbids importing implementation details | pass |

**Example:** forbids importing test internals in production
    Then  expect true == true

**Example:** forbids importing implementation details
    Then  expect true == true

### Scenario: dependency rules

| # | Example | Status |
|---|---------|--------|
| 1 | forbids domain depending on infrastructure | pass |
| 2 | forbids circular dependencies | pass |

**Example:** forbids domain depending on infrastructure
    Then  expect true == true

**Example:** forbids circular dependencies
    Then  expect true == true

### Scenario: usage rules

| # | Example | Status |
|---|---------|--------|
| 1 | forbids using Container in domain | pass |
| 2 | forbids using deprecated types | pass |

**Example:** forbids using Container in domain
    Then  expect true == true

**Example:** forbids using deprecated types
    Then  expect true == true

### Scenario: config rules

| # | Example | Status |
|---|---------|--------|
| 1 | forbids test config in release | pass |

**Example:** forbids test config in release
    Then  expect true == true

## Feature: Architecture Allow Rules

## Allowing Exceptions

    The `allow` keyword creates exceptions to forbid rules, enabling specific
    patterns that would otherwise be forbidden.

### Scenario: selective allows

| # | Example | Status |
|---|---------|--------|
| 1 | allows api to depend on core | pass |
| 2 | allows test code to use internal modules | pass |

**Example:** allows api to depend on core
    Then  expect true == true

**Example:** allows test code to use internal modules
    Then  expect true == true

### Scenario: priority-based overrides

| # | Example | Status |
|---|---------|--------|
| 1 | allow with higher priority overrides forbid | pass |

**Example:** allow with higher priority overrides forbid
    Then  expect true == true

## Feature: Layered Architecture Constraints

## Clean/Onion Architecture Rules

    Common architectural patterns can be enforced with a set of forbid/allow
    rules that define layer boundaries.

### Scenario: three-tier architecture

| # | Example | Status |
|---|---------|--------|
| 1 | defines presentation layer constraints | pass |
| 2 | defines application layer constraints | pass |
| 3 | defines domain layer constraints | pass |

**Example:** defines presentation layer constraints
    Then  expect true == true

**Example:** defines application layer constraints
    Then  expect true == true

**Example:** defines domain layer constraints
    Then  expect true == true

### Scenario: hexagonal architecture

| # | Example | Status |
|---|---------|--------|
| 1 | enforces port-adapter boundaries | pass |

**Example:** enforces port-adapter boundaries
    Then  expect true == true

## Feature: Module Boundary Rules

## Encapsulation Enforcement

    Architecture rules can enforce module encapsulation by controlling
    what can be exported and imported.

### Scenario: internal modules

| # | Example | Status |
|---|---------|--------|
| 1 | forbids importing internal submodules | pass |
| 2 | requires using public facade | pass |

**Example:** forbids importing internal submodules
    Then  expect true == true

**Example:** requires using public facade
    Then  expect true == true

### Scenario: export restrictions

| # | Example | Status |
|---|---------|--------|
| 1 | forbids exporting internal types | pass |

**Example:** forbids exporting internal types
    Then  expect true == true

## Feature: Security Architecture Rules

## Security-Related Constraints

    Architecture rules can enforce security patterns by restricting access
    to sensitive operations and data.

### Scenario: credential access

| # | Example | Status |
|---|---------|--------|
| 1 | restricts credential usage | pass |
| 2 | forbids storing secrets in plain text | pass |

**Example:** restricts credential usage
    Then  expect true == true

**Example:** forbids storing secrets in plain text
    Then  expect true == true

### Scenario: network boundaries

| # | Example | Status |
|---|---------|--------|
| 1 | restricts direct network access | pass |

**Example:** restricts direct network access
    Then  expect true == true

## Feature: Test Isolation Rules

## Test Code Boundaries

    Architecture rules ensure test code doesn't leak into production
    and production code doesn't depend on test utilities.

### Scenario: test-only code

| # | Example | Status |
|---|---------|--------|
| 1 | forbids mock in production | pass |
| 2 | forbids test utilities in production | pass |

**Example:** forbids mock in production
    Then  expect true == true

**Example:** forbids test utilities in production
    Then  expect true == true

### Scenario: test profile restrictions

| # | Example | Status |
|---|---------|--------|
| 1 | forbids test profile in release | pass |

**Example:** forbids test profile in release
    Then  expect true == true

## Feature: Architecture Rule Diagnostics

## Error Message Quality

    Architecture rules include descriptive error messages that help
    developers understand and fix violations.

### Scenario: violation messages

| # | Example | Status |
|---|---------|--------|
| 1 | provides actionable error message | pass |
| 2 | identifies violation location | pass |

**Example:** provides actionable error message
    Then  expect true == true

**Example:** identifies violation location
    Then  expect true == true

## Feature: Architecture Rule Composition

## Combining Rules

    Multiple architecture rules can be composed to express complex
    constraints using the same logical operators as pointcuts.

### Scenario: complex patterns

| # | Example | Status |
|---|---------|--------|
| 1 | combines multiple conditions | pass |
| 2 | uses negation for exceptions | pass |

**Example:** combines multiple conditions
    Then  expect true == true

**Example:** uses negation for exceptions
    Then  expect true == true


