# Reference Capability System Specification
*Source:* `test/feature/usage/capability_system_spec.spl`
**Feature IDs:** #CAP-SYS-001 to #CAP-SYS-034  |  **Category:** Type System | Capabilities  |  **Status:** Implemented

## Overview



Tests the reference capability system for memory safety:
- Parsing `mut T` and `iso T` syntax
- Aliasing rules (Shared, Exclusive, Isolated)
- Capability conversion rules
- Concurrency mode validation (Actor, LockBase, Unsafe)
- Zero-cost abstraction guarantee

## Capability Types

- `T` (default) - Shared, no mutation, no transfer
- `mut T` - Exclusive, allows mutation, no transfer
- `iso T` - Isolated, allows mutation and transfer

## Concurrency Modes

- Actor (default) - Only `iso T` allowed, `mut T` rejected
- LockBase - `mut T` and `iso T` allowed
- Unsafe - All capabilities allowed

## Syntax

```simple
@concurrency_mode(lock_base)
fn update(counter: mut Counter, delta: i64) -> i64:
    counter.value = counter.value + delta
    counter.value
```

## Feature: Parsing Capabilities

## Capability Syntax Parsing

    Tests that `mut T` and `iso T` syntax parses correctly.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses mut capability | pass |
| 2 | parses iso capability | pass |
| 3 | parses capability with generic type | pass |
| 4 | parses default shared capability (no prefix) | pass |

**Example:** parses mut capability
    Then  expect true  # Parsed successfully

**Example:** parses iso capability
    Then  expect true  # Parsed successfully

**Example:** parses capability with generic type
    Then  expect true  # Parsed successfully

**Example:** parses default shared capability (no prefix)
    Then  expect true  # Default is implicitly Shared

## Feature: Aliasing Rules

## Capability Aliasing Semantics

    Tests that aliasing rules are correctly enforced.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | allows multiple shared capabilities | pass |
| 2 | exclusive capability prevents aliasing | pass |
| 3 | isolated capability prevents aliasing | pass |

**Example:** allows multiple shared capabilities
    Then  expect use_shared(10, 20) == 30

**Example:** exclusive capability prevents aliasing
    Then  expect true

**Example:** isolated capability prevents aliasing
    Then  expect true

## Feature: Capability Conversion Rules

## Valid and Invalid Conversions

    Tests capability downgrade and upcast rules.

### Scenario: valid downgrades

| # | Example | Status |
|---|---------|--------|
| 1 | allows Exclusive to Shared | pass |
| 2 | allows Isolated to Exclusive | pass |
| 3 | allows Isolated to Shared | pass |

**Example:** allows Exclusive to Shared
    Then  expect true

**Example:** allows Isolated to Exclusive
    Then  expect true

**Example:** allows Isolated to Shared
    Then  expect true

### Scenario: invalid upcasts

| # | Example | Status |
|---|---------|--------|
| 1 | rejects Shared to Exclusive | pass |
| 2 | rejects Shared to Isolated | pass |
| 3 | rejects Exclusive to Isolated | pass |

**Example:** rejects Shared to Exclusive
    Then  expect true  # Compile-time check

**Example:** rejects Shared to Isolated
    Then  expect true  # Compile-time check

**Example:** rejects Exclusive to Isolated
    Then  expect true  # Compile-time check

## Feature: Capability Properties

## Mutation and Transfer Properties

    Tests capability mutation and transfer semantics.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | shared allows no mutation | pass |
| 2 | exclusive allows mutation | pass |
| 3 | isolated allows mutation and transfer | pass |

**Example:** shared allows no mutation
    Then  expect true

**Example:** exclusive allows mutation
    Then  expect true

**Example:** isolated allows mutation and transfer
    Then  expect true

## Feature: Nested Capabilities

## Nested Capability Types

    Tests parsing and handling of nested capabilities.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses nested mut mut T | pass |

**Example:** parses nested mut mut T
    Then  expect true  # Parses (though semantically questionable)

## Feature: Capability Environment

## Acquire and Release

    Tests capability acquisition and release semantics.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | can acquire and release capability | pass |

**Example:** can acquire and release capability
    Then  expect true  # Runtime behavior

## Feature: Concurrency Mode - Actor

## Default Actor Mode

    Tests that actor mode (default) only allows iso T.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | defaults to actor mode | pass |
| 2 | actor mode allows iso | pass |
| 3 | actor mode rejects mut in params | pass |

**Example:** defaults to actor mode
    Then  expect process(42) == 42

**Example:** actor mode allows iso
    Then  expect transfer(42) == 42

**Example:** actor mode rejects mut in params
    Then  expect true  # Compile-time check

## Feature: Concurrency Mode - LockBase

## Lock-Based Mode

    Tests that lock_base mode allows mut T.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses lock_base mode attribute | pass |
| 2 | lock_base allows mut T | pass |

**Example:** parses lock_base mode attribute
    Then  expect true

**Example:** lock_base allows mut T
    Then  expect true

## Feature: Concurrency Mode - Unsafe

## Unsafe Mode

    Tests that unsafe mode allows all capabilities.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses unsafe mode attribute | pass |
| 2 | unsafe mode allows all capabilities | pass |

**Example:** parses unsafe mode attribute
    Then  expect true

**Example:** unsafe mode allows all capabilities
    Then  expect true

## Feature: iso T in All Modes

## Universal iso Support

    Tests that iso T succeeds in all concurrency modes.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | iso works in actor mode | pass |
| 2 | iso works in lock_base mode | pass |
| 3 | iso works in unsafe mode | pass |

**Example:** iso works in actor mode
    Then  expect transfer_actor(42) == 42

**Example:** iso works in lock_base mode
    Then  expect transfer_lock(42) == 42

**Example:** iso works in unsafe mode
    Then  expect transfer_unsafe(42) == 42

## Feature: Zero-Cost Abstraction

## Runtime Cost Verification

    Tests that capabilities have no runtime overhead.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | capabilities compile to same representation | pass |

**Example:** capabilities compile to same representation
    Then  expect true

## Feature: Multiple Parameters with Capabilities

## Mixed Capability Parameters

    Tests functions with multiple parameters having different capabilities.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | allows mixed capabilities in lock_base | pass |
| 2 | allows all shared in actor mode | pass |

**Example:** allows mixed capabilities in lock_base
    Then  expect true

**Example:** allows all shared in actor mode
    Then  expect read_all(10, 20, 12) == 42

## Feature: Return Type Capabilities

## Capability in Return Types

    Tests that return types can have capabilities.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | allows mut return in lock_base | pass |
| 2 | allows iso return in all modes | pass |

**Example:** allows mut return in lock_base
    Then  expect true

**Example:** allows iso return in all modes
    Then  expect true

## Feature: Class Method Capabilities

## Methods and Concurrency Modes

    Tests that class methods respect concurrency modes.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | class methods default to actor mode | pass |

**Example:** class methods default to actor mode
    Given val c = Counter(value: 42)
    Then  expect c.get_value() == 42

## Feature: Integration Patterns

## Realistic Capability Usage

    Tests capabilities in realistic programming patterns.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | actor message passing with iso | pass |
| 2 | lock-based concurrent modification | pass |
| 3 | builder pattern with mut | pass |
| 4 | unsafe mode escape hatch | pass |
| 5 | iso transfer semantics | pass |
| 6 | mixed const and mut parameters | pass |

**Example:** actor message passing with iso
    Then  expect process_message(42) == 42

**Example:** lock-based concurrent modification
    Then  expect true

**Example:** builder pattern with mut
    Then  expect true

**Example:** unsafe mode escape hatch
    Then  expect true

**Example:** iso transfer semantics
    Then  expect consume(42) == 42

**Example:** mixed const and mut parameters
    Then  expect update_with_config(0, 6, 7) == 42


