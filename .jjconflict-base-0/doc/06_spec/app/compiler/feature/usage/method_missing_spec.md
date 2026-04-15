# Method Missing Handler Specification

Tests for the method_missing dynamic dispatch mechanism that allows objects to handle calls to undefined methods at runtime through a catch-all handler.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TBD |
| Category | Language |
| Difficulty | 3/5 |
| Status | Planned |
| Source | `test/feature/usage/method_missing_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests for the method_missing dynamic dispatch mechanism that allows objects
to handle calls to undefined methods at runtime through a catch-all handler.

## Syntax

```simple
class DynamicHandler:
fn method_missing(name: text, args: List) -> Any:
print "Called {name} with {args}"
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Dynamic Dispatch | Runtime method resolution for undefined methods |
| Method Missing | Catch-all handler for unimplemented methods |
| Reflection | Access to method name and arguments at runtime |
| Fallback Behavior | Default handling when method doesn't exist |

## Behavior

- method_missing is called when a method is not found on an object
- Receives method name and argument list as parameters
- Allows runtime behavior customization and dynamic APIs
- Can raise errors or provide default implementations
- Integration with reflection and introspection

## Related Specifications

- Dynamic Typing - Runtime type behavior
- Reflection - Introspection capabilities
- Error Handling - Exception propagation from method_missing

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/method_missing/result.json` |

## Scenarios

- placeholder test
- placeholder test
- placeholder test
