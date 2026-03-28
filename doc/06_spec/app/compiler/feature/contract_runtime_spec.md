# Contract Runtime Specification

**Feature ID:** #CONTRACT-RT-001 to #CONTRACT-RT-031 | **Category:** Type System | Contracts | **Status:** Implemented

_Source: `test/feature/usage/contract_runtime_spec.spl`_

---

## Contract Syntax

```simple
fn transfer(from: i64, to: i64, amount: i64) -> (i64, i64):
    in:
        amount > 0
        from >= amount
    invariant:
        from >= 0
        to >= 0
    out(res):
        res.0 == old(from) - amount
        res.1 == old(to) + amount
    # function body
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 25 |

## Test Structure

### Basic old() Capture

- ✅ captures simple parameter value
- ✅ captures multiple parameters
- ✅ captures field access
- ✅ captures complex expression
### Precondition Lowering

- ✅ validates basic precondition
- ✅ validates multiple preconditions
### Postcondition Lowering

- ✅ validates basic postcondition
- ✅ validates multiple postconditions
### Invariant Lowering

- ✅ validates basic invariant
### Combined Contracts with old()

- ✅ validates transfer function
- ✅ validates custom binding in postcondition
### Multiple old() References

- ✅ handles multiple references to same old()
- ✅ handles old() with different params
### Error Postconditions

- ✅ parses error postcondition
- ✅ validates success and error postconditions
### Complex Contract Scenarios

- ✅ validates nested old expressions
- ✅ validates arithmetic contracts
- ✅ validates comparison chain contracts
### All Contract Types Together

- ✅ validates full contract
### Contract with Boolean Logic

- ✅ validates boolean logic contract
- ✅ validates negation contract
### Contract with Conditionals

- ✅ validates conditional contract
- ✅ validates early return contract
### old() with Arithmetic Expressions

- ✅ captures arithmetic in old()
- ✅ references parameter in postcondition

