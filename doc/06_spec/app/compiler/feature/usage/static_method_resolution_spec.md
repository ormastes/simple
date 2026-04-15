# Static Method Resolution

Tests static method resolution and calling in interpreter mode. Uses ClassName.method() dot-access syntax which works in closures.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RESOLVE-001 |
| Category | Compiler |
| Status | Active |
| Source | `test/feature/usage/static_method_resolution_spec.spl` |
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

## Overview

Tests static method resolution and calling in interpreter mode.
Uses ClassName.method() dot-access syntax which works in closures.

## Syntax

```simple
class Point:
    x: i64
    y: i64
    static fn origin() -> Point:
        Point(x: 0, y: 0)
val p = Point.origin()
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/static_method_resolution/result.json` |

## Scenarios

- resolves simple static method call
- resolves static method with parameters
- resolves static method returning object
- correctly resolves static method vs instance method
- allows same name for static and instance methods
- chains static method call with instance method
- calls multiple static methods in sequence
- static method calls another static method
- static method creates object and calls instance method
- resolves static method on struct
- resolves multiple static methods on struct
