# Guard Clause Specification

Guard clauses (pattern guards) allow conditional matching within pattern match arms.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GUARD-CLAUSE |
| Category | Syntax |
| Status | Implemented |
| Source | `test/feature/usage/guard_clause_spec.spl` |
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

Guard clauses (pattern guards) allow conditional matching within pattern match arms.
They combine pattern matching with boolean conditions using the `if` keyword after
the pattern to provide additional filtering before the arm body executes.

## Syntax

```simple
match value:
case pattern if condition:
body
```

## Key Behaviors

- Guard conditions are evaluated after pattern matching succeeds
- Variables bound in the pattern are available in the guard condition
- If the guard evaluates to false, matching continues to the next arm
- Guards can reference external variables from the enclosing scope

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/guard_clause/result.json` |

## Scenarios

- matches when guard is true
- falls through when guard is false
- reaches default case when all guards fail
- matches exact value via guard
- uses bound variables in guard
- guards with multiple comparisons
- filters enum payload with guard
- references variables from outer scope
- uses modulo in guard
- uses logical or in guard
