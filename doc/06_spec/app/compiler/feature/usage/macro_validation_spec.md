# Macro Validation Specification

Tests that macros can be validated without full expansion in LL(1) parsing:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MACRO-VAL-001 to #MACRO-VAL-014 |
| Category | Infrastructure \| Macros |
| Status | Implemented |
| Source | `test/feature/usage/macro_validation_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests that macros can be validated without full expansion in LL(1) parsing:
- Ordering validation (defined before use)
- Shadowing detection (intro symbols)
- QIDENT template variable validation
- Type annotation requirements

## Error Codes

- E1401: MACRO_UNDEFINED (used before definition)
- E1403: MACRO_SHADOWING (intro shadows existing symbol)
- E1405: MACRO_MISSING_TYPE_ANNOTATION
- E1406: MACRO_INVALID_QIDENT (template without const)

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/macro_validation/result.json` |

## Scenarios

- succeeds when macro is defined before use
- fails when macro is used before definition
- fails when intro shadows existing variable
- fails when intro shadows existing function
- succeeds when intro introduces different symbol
- succeeds with const parameter in template
- fails when template variable is not const
- fails when intro let lacks type annotation
- succeeds when intro let has type annotation
- allows using macros in any order after definition
- allows single intro symbol
- fails when macro introduces duplicate symbols
- generates symbols from const for loop
- selects symbols based on const condition
