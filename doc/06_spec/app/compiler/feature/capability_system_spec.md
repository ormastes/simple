# Reference Capability System Specification

**Feature ID:** #CAP-SYS-001 to #CAP-SYS-034 | **Category:** Type System | Capabilities | **Status:** Implemented

_Source: `test/feature/usage/capability_system_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 40 |

## Test Structure

### Parsing Capabilities

- ✅ parses mut capability
- ✅ parses iso capability
- ✅ parses capability with generic type
- ✅ parses default shared capability (no prefix)
### Aliasing Rules

- ✅ allows multiple shared capabilities
- ✅ exclusive capability prevents aliasing
- ✅ isolated capability prevents aliasing
### Capability Conversion Rules

#### valid downgrades

- ✅ allows Exclusive to Shared
- ✅ allows Isolated to Exclusive
- ✅ allows Isolated to Shared
#### invalid upcasts

- ✅ rejects Shared to Exclusive
- ✅ rejects Shared to Isolated
- ✅ rejects Exclusive to Isolated
### Capability Properties

- ✅ shared allows no mutation
- ✅ exclusive allows mutation
- ✅ isolated allows mutation and transfer
### Nested Capabilities

- ✅ parses nested mut mut T
### Capability Environment

- ✅ can acquire and release capability
### Concurrency Mode - Actor

- ✅ defaults to actor mode
- ✅ actor mode allows iso
- ✅ actor mode rejects mut in params
### Concurrency Mode - LockBase

- ✅ parses lock_base mode attribute
- ✅ lock_base allows mut T
### Concurrency Mode - Unsafe

- ✅ parses unsafe mode attribute
- ✅ unsafe mode allows all capabilities
### iso T in All Modes

- ✅ iso works in actor mode
- ✅ iso works in lock_base mode
- ✅ iso works in unsafe mode
### Zero-Cost Abstraction

- ✅ capabilities compile to same representation
### Multiple Parameters with Capabilities

- ✅ allows mixed capabilities in lock_base
- ✅ allows all shared in actor mode
### Return Type Capabilities

- ✅ allows mut return in lock_base
- ✅ allows iso return in all modes
### Class Method Capabilities

- ✅ class methods default to actor mode
### Integration Patterns

- ✅ actor message passing with iso
- ✅ lock-based concurrent modification
- ✅ builder pattern with mut
- ✅ unsafe mode escape hatch
- ✅ iso transfer semantics
- ✅ mixed const and mut parameters

