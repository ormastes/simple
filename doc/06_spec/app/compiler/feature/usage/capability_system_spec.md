# Reference Capability System Specification

Tests the reference capability system for memory safety:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CAP-SYS-001 to #CAP-SYS-034 |
| Category | Type System \| Capabilities |
| Status | Implemented |
| Source | `test/feature/usage/capability_system_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 40 |
| Active scenarios | 40 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

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

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/capability_system/result.json` |

## Scenarios

- parses mut capability
- parses iso capability
- parses capability with generic type
- parses default shared capability (no prefix)
- allows multiple shared capabilities
- exclusive capability prevents aliasing
- isolated capability prevents aliasing
- allows Exclusive to Shared
- allows Isolated to Exclusive
- allows Isolated to Shared
- rejects Shared to Exclusive
- rejects Shared to Isolated
- rejects Exclusive to Isolated
- shared allows no mutation
- exclusive allows mutation
- isolated allows mutation and transfer
- parses nested mut mut T
- can acquire and release capability
- defaults to actor mode
- actor mode allows iso
- actor mode rejects mut in params
- parses lock_base mode attribute
- lock_base allows mut T
- parses unsafe mode attribute
- unsafe mode allows all capabilities
- iso works in actor mode
- iso works in lock_base mode
- iso works in unsafe mode
- capabilities compile to same representation
- allows mixed capabilities in lock_base
- allows all shared in actor mode
- allows mut return in lock_base
- allows iso return in all modes
- class methods default to actor mode
- actor message passing with iso
- lock-based concurrent modification
- builder pattern with mut
- unsafe mode escape hatch
- iso transfer semantics
- mixed const and mut parameters
