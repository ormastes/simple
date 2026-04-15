# Elif Val/Var Pattern Binding Specification

Tests for `elif val`/`elif var` pattern binding in conditional branches. Verifies that pattern matching works correctly in elif positions, matching the existing `if val` support.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1001 |
| Category | Language |
| Status | Implemented |
| Source | `test/feature/usage/elif_val_pattern_binding_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests for `elif val`/`elif var` pattern binding in conditional branches.
Verifies that pattern matching works correctly in elif positions,
matching the existing `if val` support.

## Syntax

```simple
if val Some(x) = expr1:
use(x)
elif val Some(y) = expr2:
use(y)
elif condition:
fallback()
else:
default()
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/elif_val_pattern_binding/result.json` |

## Scenarios

- matches elif val when if condition is false
- skips elif val when pattern does not match
- binds variable from elif val pattern
- falls to else when elif val does not match
- does not reach else when elif val matches
- matches first elif val pattern
- matches second elif val when first does not match
- falls through all elif val when none match
- matches regular elif before elif val
- matches elif val after failed regular elif
- matches regular elif after failed elif val
- reaches else after mixed elif failures
- matches if val and skips elif val
- skips if val and matches elif val
- skips both if val and elif val to else
- matches nested Some in elif val
- chains multiple Some patterns
- returns from elif val branch
- bindings do not leak to outer scope
- returns nil when no branch matches
