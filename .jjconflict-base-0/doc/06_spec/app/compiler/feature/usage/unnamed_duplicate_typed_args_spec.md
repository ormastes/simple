# Unnamed Duplicate Typed Arguments Warning Specification

This lint warns when a function has multiple parameters of the same type that

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LINT-001 |
| Category | Lint |
| Status | Implemented |
| Source | `test/feature/usage/unnamed_duplicate_typed_args_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

This lint warns when a function has multiple parameters of the same type that
are passed positionally without named arguments. This helps prevent argument
order mistakes at call sites by encouraging explicit naming.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/unnamed_duplicate_typed_args/result.json` |

## Scenarios

- warns on positional call with two text params
- accepts named arguments without warning
- works with mixed named and positional args
- does not warn on single parameter
- does not warn on different typed params
- does not warn when all params are named
- copy function with named args
- compare function with named args
- move function with named args
