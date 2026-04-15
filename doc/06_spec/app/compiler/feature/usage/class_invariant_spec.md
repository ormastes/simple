# Class Invariant Specification

Tests that class invariants are properly checked:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CONTRACT-INV-001 to #CONTRACT-INV-018 |
| Category | Type System \| Contracts |
| Status | Implemented |
| Source | `test/feature/usage/class_invariant_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests that class invariants are properly checked:
- After constructor execution (even if constructor is private)
- Before/after public method execution
- NOT checked for private methods

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

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/class_invariant/result.json` |

## Scenarios

- checks invariant after constructor
- checks multiple invariants after constructor
- private constructor gets invariant check
- constructor with precondition and invariant
- public method checks invariants
- private method skips invariants
- complex invariant with field comparison
- separate invariants per class
- class without invariant works
- invariant can reference pure methods
- explicitly public constructor gets invariants
- constructor detected by name
- bank account with full contracts
- factory methods get invariants
- struct has invariant checks
