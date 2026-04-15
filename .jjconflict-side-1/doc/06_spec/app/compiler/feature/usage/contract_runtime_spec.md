# Contract Runtime Specification

Tests that contract checks execute correctly at runtime, including

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CONTRACT-RT-001 to #CONTRACT-RT-031 |
| Category | Type System \| Contracts |
| Status | Implemented |
| Source | `test/feature/usage/contract_runtime_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests that contract checks execute correctly at runtime, including
preconditions, postconditions, invariants, and old() capture.

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
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/contract_runtime/result.json` |

## Scenarios

- captures simple parameter value
- captures multiple parameters
- captures field access
- captures complex expression
- validates basic precondition
- validates multiple preconditions
- validates basic postcondition
- validates multiple postconditions
- validates basic invariant
- validates transfer function
- validates custom binding in postcondition
- handles multiple references to same old()
- handles old() with different params
- parses error postcondition
- validates success and error postconditions
- validates nested old expressions
- validates arithmetic contracts
- validates comparison chain contracts
- validates full contract
- validates boolean logic contract
- validates negation contract
- validates conditional contract
- validates early return contract
- captures arithmetic in old()
- references parameter in postcondition
