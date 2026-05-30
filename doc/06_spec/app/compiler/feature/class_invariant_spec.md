# Class Invariant Specification

**Feature ID:** #CONTRACT-INV-001 to #CONTRACT-INV-018 | **Category:** Type System | Contracts | **Status:** Implemented

_Source: `test/feature/usage/class_invariant_spec.spl`_

---

## Syntax

```simple
class Counter:
    value: i64

    invariant:
        self.value >= 0

    static fn new() -> Counter:
        Counter(value: 0)

    me increment():
        self.value = self.value + 1
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 16 |

## Test Structure

### Constructor Invariant Checks

- ✅ checks invariant after constructor
- ✅ checks multiple invariants after constructor
- ✅ private constructor gets invariant check
- ✅ constructor with precondition and invariant
### Public Method Invariant Checks

- ✅ public method checks invariants
- ✅ private method skips invariants
- ✅ complex invariant with field comparison
### Multiple Classes with Invariants

- ✅ separate invariants per class
### Inheritance and Invariants

- ✅ child maintains parent invariant
### Class Invariant Edge Cases

- ✅ class without invariant works
- ✅ invariant can reference pure methods
### Constructor Visibility

- ✅ explicitly public constructor gets invariants
- ✅ constructor detected by name
### Complete Class Contract Integration

- ✅ bank account with full contracts
### Factory Method Invariants

- ✅ factory methods get invariants
### Struct Invariants

- ✅ struct has invariant checks

