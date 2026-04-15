# Classes and Object-Oriented Programming Specification

Tests for class definitions, instance creation, field access, methods, impl blocks, context blocks, method_missing, auto-forwarding properties, and static polymorphism with interface bindings.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OOP-001 |
| Category | Language \| Classes |
| Status | Implemented |
| Source | `test/feature/usage/classes_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests for class definitions, instance creation, field access, methods,
impl blocks, context blocks, method_missing, auto-forwarding properties,
and static polymorphism with interface bindings.

## Syntax

```simple
class Calculator:
static fn add(a, b):
return a + b

struct Point:
x: i64
y: i64

impl Point:
fn sum(self):
return self.x + self.y

context obj:
method()  # Dispatches to obj.method()
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/classes/result.json` |

## Scenarios

- calls static method on class
- calls multiple static methods
- adds method to struct via impl
- adds method with arguments via impl
- creates instances with direct construction
- accesses string field
- creates class with default field values
- calls instance method
- calls method with arguments
- dispatches method to context object
- accesses self fields in context method
- calls method_missing for unknown method
- passes arguments to method_missing
- uses method_missing in context block
- gets property via get_ method
- sets property via set_ method returning new instance
- checks boolean property via is_ method
- uses combined getter and setter
- binds trait to concrete class
- binds trait with multiple methods
- binds trait with fields
- passes bound trait as function parameter
- calculates different areas via Shape trait
