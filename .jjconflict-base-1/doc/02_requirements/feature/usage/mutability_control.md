# Mutability Control Specification
*Source:* `test/feature/usage/mutability_control_spec.spl`
**Feature IDs:** #TBD  |  **Category:** Language  |  **Status:** Planned

## Overview



## Overview

Tests for mutability control mechanisms including mutable and immutable
references, capability-based access control, and field mutation rules.

## Syntax

```simple
val immutable_list = [1, 2, 3]       # Immutable binding
var mutable_counter = 0               # Mutable binding
obj.field = new_value                 # Field mutation
me mutate_self(value):                # Mutable method
    self.state = value
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| val/var | Immutable and mutable variable bindings |
| me Method | Method with permission to mutate self |
| Reference Capabilities | Fine-grained control over access and modification |
| Frozen Objects | Objects that cannot be modified after creation |
| Mutation Safety | Compile-time verification of mutation correctness |

## Behavior

- val bindings are immutable and cannot be reassigned
- var bindings can be reassigned and modified
- Methods marked with me can modify their receiver object
- Regular methods cannot modify their receiver (immutable self)
- Nested mutability follows capability rules
- Field access and modification checked at compile time

## Related Specifications

- Reference Capabilities - Memory safety model
- Type System - Mutability as part of type information
- Classes and Structs - Object state management

## Feature: Mutability Control Basic Usage

## Variable Mutability

    Verifies that val/var bindings respect mutability rules
    and prevent invalid mutations at compile-time.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | placeholder test | pass |

**Example:** placeholder test
    Then  expect true

## Feature: Mutability Control in Methods

## Method-based Mutation

    Tests me methods vs regular methods, self mutation permissions,
    and compile-time enforcement of mutation safety.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | placeholder test | pass |

**Example:** placeholder test
    Then  expect true

## Feature: Mutability Control Reference Capabilities

## Advanced Capability Control

    Tests fine-grained mutability control through capabilities,
    frozen objects, and complex mutation scenarios.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | placeholder test | pass |

**Example:** placeholder test
    Then  expect true


