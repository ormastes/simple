# Dependency Injection Specification

Integration tests for DI Container with realistic service patterns.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DI-INJ-001 to #DI-INJ-007 |
| Category | Runtime \| Dependency Injection |
| Status | Implemented |
| Source | `test/feature/usage/di_injection_spec.spl` |
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

**Tags:** di, integration

Integration tests for DI Container with realistic service patterns.
Tests focus on scenarios not covered by unit tests.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/di_injection/result.json` |

## Scenarios

- creates service with repository dependency
- chains multiple text dependencies
- profile enum converts to text
- profile enum parses from text
- profile defaults to dev for unknown
- all profiles have unique names
- stores and retrieves values
- has returns true for existing keys
- get returns None for missing keys
- set overwrites existing values
- returns Ok for existing binding
- returns Err for missing binding
- function with @inject is parsed
- class method with @inject is parsed
