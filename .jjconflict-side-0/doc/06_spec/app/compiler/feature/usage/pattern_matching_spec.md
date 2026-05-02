# Pattern Matching Specification

Pattern matching provides a way to extract and deconstruct values using patterns.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PATTERN-MATCH |
| Category | Language |
| Status | Implemented |
| Source | `test/feature/usage/pattern_matching_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Pattern matching provides a way to extract and deconstruct values using patterns.

## Key Behaviors

- Pattern matching deconstructs values into their components
- Variables bound in patterns are available in match arm bodies
- Patterns include literals, enums, tuples, records, and wildcards

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/pattern_matching/result.json` |

## Scenarios

- matches exact literal values
- matches with wildcard pattern
- binds value to variable
- matches tuple and extracts elements
- matches nested tuples
- matches with partial wildcard
- matches Option Some variant
- matches Option None variant
- matches Result Ok variant
- uses match as expression
- matches multiple patterns
