# AOP Pointcut Expression Specification

Pointcut expressions define where advice should be applied. The `pc{...}` syntactic

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #AOP-PC-001 to #AOP-PC-015 |
| Category | Language |
| Status | In Progress |
| Source | `test/feature/usage/aop_pointcut_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

**Tags:** aop

Pointcut expressions define where advice should be applied. The `pc{...}` syntactic
island contains pointcut predicates that match against the program structure.

## Syntax

```simple
pc{ selector(pattern) }
pc{ selector1(...) & selector2(...) }  # AND
pc{ selector1(...) | selector2(...) }  # OR
pc{ !selector(...) }                   # NOT
```

## Selectors

| Selector | Description | Example |
|----------|-------------|---------|
| execution | Match function execution | `execution(* foo(..))` |
| within | Match code in module/class | `within(services.*)` |
| attr | Match by attribute | `attr(logged)` |

## Limitations (Current Implementation)

- Init selector not yet implemented (requires around advice)
- Inline module definitions in test blocks not supported

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/aop_pointcut/result.json` |

## Scenarios

- matches any return type with wildcard
- matches exact function name
- matches prefix wildcard
- matches suffix wildcard
- matches any parameters with (..)
- matches function with attribute
- matches multiple attributes
- requires both conditions
- matches either condition
- excludes matching pointcuts
- matches prefix with name*
- matches suffix with *name
