# Mutability Control Specification

**Feature ID:** #TBD | **Category:** Language | **Difficulty:** 3/5 | **Status:** Planned

_Source: `test/feature/usage/mutability_control_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 3 |

## Test Structure

### Mutability Control Basic Usage

- ✅ placeholder test
### Mutability Control in Methods

- ✅ placeholder test
### Mutability Control Reference Capabilities

- ✅ placeholder test

