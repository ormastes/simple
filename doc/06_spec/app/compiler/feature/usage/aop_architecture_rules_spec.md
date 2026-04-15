# AOP Architecture Rules Specification

Architecture rules enforce structural constraints on the codebase using the same

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #AOP-ARCH-001 to #AOP-ARCH-010 |
| Category | Language |
| Status | Implemented |
| Source | `test/feature/usage/aop_architecture_rules_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Architecture rules enforce structural constraints on the codebase using the same
unified predicate grammar as AOP. Rules are validated at compile time and can
forbid or allow certain dependency patterns.

## Syntax

```simple
forbid pc{ import(from_pattern, to_pattern) } "Error message"
forbid pc{ depend(from_pattern, to_pattern) } "Error message"

allow pc{ depend(within(api.**), within(core.**)) } "Allowed exception"
```

## Architecture Selectors

| Selector | Description |
|----------|-------------|
| import(from, to) | Match import statements |
| depend(from, to) | Match module dependencies |
| use(pattern) | Match type/function usage |
| export(pattern) | Match exported symbols |
| config(string) | Match configuration values |

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/aop_architecture_rules/result.json` |

## Scenarios

- forbids importing test internals in production
- forbids importing implementation details
- forbids domain depending on infrastructure
- forbids circular dependencies
- forbids using Container in domain
- forbids using deprecated types
- forbids test config in release
- allows api to depend on core
- allows test code to use internal modules
- allow with higher priority overrides forbid
- defines presentation layer constraints
- defines application layer constraints
- defines domain layer constraints
- enforces port-adapter boundaries
- forbids importing internal submodules
- requires using public facade
- forbids exporting internal types
- restricts credential usage
- forbids storing secrets in plain text
- restricts direct network access
- forbids mock in production
- forbids test utilities in production
- forbids test profile in release
- provides actionable error message
- identifies violation location
- combines multiple conditions
- uses negation for exceptions
