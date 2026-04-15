# Assert Statement Specification

Tests assert statement support including:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #ASSERT-001 to #ASSERT-012 |
| Category | Language \| Contracts |
| Status | Implemented |
| Source | `test/feature/usage/assert_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests assert statement support including:
- Basic assert with boolean condition
- Assert with custom error message
- Assert in functions
- Assert with expressions and boolean logic
- Assert in control flow (if blocks, loops)
- Assert combined with function contracts

## Syntax

```simple
expect(x > 0).to_equal(true)

expect(x > 0, "x must be positive").to_equal(true)

fn validate(x: i64) -> i64:
expect(x >= 0, "input must be non-negative").to_equal(true)
x * 2
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/assert/result.json` |

## Scenarios

- basic assert compiles
- assert with message compiles
- multiple assert conditions
- assert in function body
- multiple asserts in function
- assert with comparison
- assert with boolean logic
- assert in if block
- assert in loop
- assert combined with contracts
